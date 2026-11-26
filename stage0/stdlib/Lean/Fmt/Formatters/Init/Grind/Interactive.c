// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Grind.Interactive
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Init.Tactics meta import Init.Grind.Interactive meta import Init.Grind.Attr import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_tacticOptConfigItems___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_nl;
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSimpLikeWithGenericConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtRwLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtCaseDeclaration___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNextLike___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindAnchor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtGrindAnchor___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGrindAnchor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtGrindAnchor___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindAnchor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtGrindAnchor___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindAnchor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "anchor"};
static const lean_object* l_Lean_Fmt_fmtGrindAnchor___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnchor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnchor___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnchor___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnchor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(168, 155, 228, 98, 168, 72, 115, 174)}};
static const lean_object* l_Lean_Fmt_fmtGrindAnchor___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtGrindAnchor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l_Lean_Fmt_fmtGrindAnchor___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnchor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l_Lean_Fmt_fmtGrindAnchor___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnchor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnchor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtGrindAnchor"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(173, 202, 114, 247, 168, 156, 159, 6)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindLemma"};
static const lean_object* l_Lean_Fmt_fmtGrindLemma___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemma___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemma___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemma___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 180, 24, 243, 113, 54, 79, 133)}};
static const lean_object* l_Lean_Fmt_fmtGrindLemma___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindLemma___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Fmt_fmtGrindLemma___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindLemma___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Fmt_fmtGrindLemma___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemma___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemma___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemma___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemma___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Fmt_fmtGrindLemma___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindLemma___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLemma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLemma___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindLemma"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 209, 142, 113, 249, 20, 124, 122)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindLemmaMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLemmaMin"};
static const lean_object* l_Lean_Fmt_fmtGrindLemmaMin___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindLemmaMin___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemmaMin___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemmaMin___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemmaMin___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemmaMin___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemmaMin___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLemmaMin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLemmaMin___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindLemmaMin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 124, 255, 191, 121, 182, 88, 219)}};
static const lean_object* l_Lean_Fmt_fmtGrindLemmaMin___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindLemmaMin___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLemmaMin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLemmaMin___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindLemmaMin"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 97, 153, 94, 87, 52, 209, 102)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindErase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindErase"};
static const lean_object* l_Lean_Fmt_fmtGrindErase___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindErase___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindErase___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindErase___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindErase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 172, 113, 174, 15, 5, 26, 121)}};
static const lean_object* l_Lean_Fmt_fmtGrindErase___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindErase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtGrindErase___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindErase___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtGrindErase___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindErase___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindErase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindErase___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindErase"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 135, 55, 144, 122, 132, 114, 108)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindParam___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindParam"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 144, 208, 205, 52, 106, 220, 83)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindParam"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 209, 134, 178, 167, 181, 53, 86)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindThmNs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Fmt_fmtGrindThmNs___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGrindThmNs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "thmNs"};
static const lean_object* l_Lean_Fmt_fmtGrindThmNs___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindThmNs___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindThmNs___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindThmNs___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindThmNs___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindThmNs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__2_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 18, 142, 106, 37, 179, 0, 161)}};
static const lean_object* l_Lean_Fmt_fmtGrindThmNs___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindThmNs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindThmNs___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindThmNs"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 61, 15, 159, 232, 128, 145, 237)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindThm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindThm___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 175, 92, 250, 215, 173, 92, 62)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindThm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(23, 189, 141, 229, 96, 182, 164, 166)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grind_filter_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterIdent___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterIdent___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 183, 54, 132, 193, 221, 83, 246)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterIdent___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterIdent___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterIdent___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFilterIdent"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 157, 94, 49, 252, 23, 45, 204)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenCmp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenCmp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenCmp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen<_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenLt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 91, 104, 32, 61, 131, 243, 196)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenLt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenLt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenLt___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenLt___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLt___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFilterGenLt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 196, 46, 16, 72, 39, 118, 93)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen=_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenEq___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenEq___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 110, 208, 13, 150, 123, 60, 151)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenEq___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenEq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFilterGenEq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 175, 238, 167, 64, 88, 201, 98)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenNe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen!=_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenNe___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenNe___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenNe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 149, 94, 94, 69, 234, 169, 170)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenNe___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenNe___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenNe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenNe___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFilterGenNe"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 85, 120, 200, 11, 233, 255, 147)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenLe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 17, .m_data = "grind_filterGen≤_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenLe___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLe___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 191, 11, 181, 243, 245, 215, 191)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenLe___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLe___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLe___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFilterGenLe"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 152, 159, 90, 150, 255, 83, 45)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen<=_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 96, 49, 75, 137, 142, 109, 186)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLeAscii(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLeAscii___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtGrindFilterGenLeAscii"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 5, 231, 139, 22, 38, 99, 132)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenGt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen>_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenGt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 245, 163, 142, 72, 168, 216, 63)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenGt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFilterGenGt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 214, 229, 42, 118, 24, 65, 111)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenGe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 17, .m_data = "grind_filterGen≥_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenGe___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGe___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 138, 8, 224, 7, 211, 129, 34)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenGe___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGe___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGe___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFilterGenGe"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 8, 124, 134, 244, 41, 245, 105)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen>=_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 129, 153, 143, 173, 111, 170, 63)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGeAscii(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGeAscii___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtGrindFilterGenGeAscii"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 15, 67, 70, 179, 39, 185, 18)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grind_filter(_)"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterParen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterParen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterParen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterParen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterParen___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 150, 229, 147, 17, 198, 129, 17)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFilterParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 56, 41, 55, 233, 56, 70, 46)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grind_filter_&&_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterAnd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterAnd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 18, 222, 93, 166, 92, 88, 35)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterAnd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterAnd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterAnd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterAnd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindFilterAnd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 80, 223, 168, 91, 193, 161, 4)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grind_filter_||_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterOr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterOr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterOr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterOr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterOr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterOr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterOr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterOr___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterOr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterOr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterOr___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterOr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 127, 248, 101, 151, 207, 64, 193)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterOr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterOr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterOr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterOr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindFilterOr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 2, 59, 33, 41, 20, 112, 139)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilterNot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_filter!_"};
static const lean_object* l_Lean_Fmt_fmtGrindFilterNot___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterNot___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterNot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterNot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterNot___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterNot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterNot___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterNot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterNot___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilterNot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilterNot___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilterNot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 240, 71, 91, 236, 83, 171, 27)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilterNot___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilterNot___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterNot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterNot___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindFilterNot"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 88, 1, 154, 176, 126, 198, 95)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindFilter"};
static const lean_object* l_Lean_Fmt_fmtGrindFilter___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilter___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilter___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilter___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilter___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilter___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFilter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFilter___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFilter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 133, 155, 61, 50, 240, 42, 169)}};
static const lean_object* l_Lean_Fmt_fmtGrindFilter___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFilter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilter___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtGrindFilter"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 183, 157, 116, 1, 22, 239, 126)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindRefAnchor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_ref_"};
static const lean_object* l_Lean_Fmt_fmtGrindRefAnchor___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindRefAnchor___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 234, 46, 225, 9, 69, 165, 154)}};
static const lean_object* l_Lean_Fmt_fmtGrindRefAnchor___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindRefAnchor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefAnchor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefAnchor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindRefAnchor"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 116, 187, 200, 144, 1, 232, 139)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_ref__/__"};
static const lean_object* l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 78, 76, 1, 128, 192, 165, 233)}};
static const lean_object* l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefAnchordOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefAnchordOrd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtGrindRefAnchordOrd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 201, 80, 9, 10, 156, 195, 65)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindRefTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grind_ref__1"};
static const lean_object* l_Lean_Fmt_fmtGrindRefTerm___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindRefTerm___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefTerm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefTerm___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefTerm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefTerm___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefTerm___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefTerm___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRefTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRefTerm___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindRefTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 215, 110, 75, 133, 130, 84, 131)}};
static const lean_object* l_Lean_Fmt_fmtGrindRefTerm___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindRefTerm___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefTerm___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGrindRefTerm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 64, 112, 168, 20, 40, 198, 208)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_fmtGrindStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_nested, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtGrindStep___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindStep___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_fmtGrindStep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtGrindStep___closed__1;
static const lean_string_object l_Lean_Fmt_fmtGrindStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindStep"};
static const lean_object* l_Lean_Fmt_fmtGrindStep___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindStep___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindStep___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindStep___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindStep___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindStep___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindStep___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindStep___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindStep___closed__3_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 239, 5, 217, 230, 199, 187, 87)}};
static const lean_object* l_Lean_Fmt_fmtGrindStep___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindStep___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindStep___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGrindStep"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 81, 29, 6, 89, 197, 200, 246)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSeq1Indented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeq1Indented"};
static const lean_object* l_Lean_Fmt_fmtGrindSeq1Indented___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeq1Indented___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 114, 22, 139, 17, 175, 241, 184)}};
static const lean_object* l_Lean_Fmt_fmtGrindSeq1Indented___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeq1Indented___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindSeq1Indented___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Fmt_fmtGrindSeq1Indented___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeq1Indented___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeq1Indented(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeq1Indented___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtGrindSeq1Indented"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 89, 60, 196, 23, 93, 54, 239)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeqBracketed"};
static const lean_object* l_Lean_Fmt_fmtGrindSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeqBracketed___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 10, 37, 72, 63, 213, 137, 199)}};
static const lean_object* l_Lean_Fmt_fmtGrindSeqBracketed___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeqBracketed___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeqBracketed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeqBracketed___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtGrindSeqBracketed"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 182, 46, 148, 165, 145, 13, 33)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l_Lean_Fmt_fmtGrindSeq___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeq___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeq___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeq___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeq___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeq___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l_Lean_Fmt_fmtGrindSeq___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindSeq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 48, 107, 63, 0, 247, 39)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtGrindKeywordFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGrindKeywordFilter___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindKeywordFilter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindKeywordFilter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindKeywordFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindShowAsserted___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "showAsserted"};
static const lean_object* l_Lean_Fmt_fmtGrindShowAsserted___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowAsserted___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 9, 52, 210, 246, 83, 42, 129)}};
static const lean_object* l_Lean_Fmt_fmtGrindShowAsserted___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowAsserted___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowAsserted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowAsserted___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtGrindShowAsserted"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 7, 184, 211, 25, 233, 115, 69)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindShowTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTrue"};
static const lean_object* l_Lean_Fmt_fmtGrindShowTrue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowTrue___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTrue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowTrue___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTrue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowTrue___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTrue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowTrue___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowTrue___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindShowTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 221, 230, 107, 62, 158, 128, 182)}};
static const lean_object* l_Lean_Fmt_fmtGrindShowTrue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowTrue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowTrue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowTrue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindShowTrue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 128, 118, 221, 113, 63, 222, 112)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindShowFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showFalse"};
static const lean_object* l_Lean_Fmt_fmtGrindShowFalse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowFalse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowFalse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowFalse___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindShowFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 23, 10, 157, 249, 80, 147, 23)}};
static const lean_object* l_Lean_Fmt_fmtGrindShowFalse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowFalse___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowFalse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowFalse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindShowFalse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 235, 192, 182, 11, 222, 113, 169)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindShowEqcs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showEqcs"};
static const lean_object* l_Lean_Fmt_fmtGrindShowEqcs___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowEqcs___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindShowEqcs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 148, 3, 250, 60, 240, 18, 216)}};
static const lean_object* l_Lean_Fmt_fmtGrindShowEqcs___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowEqcs___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowEqcs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowEqcs___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindShowEqcs"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 74, 80, 37, 190, 153, 111, 83)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindShowCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showCases"};
static const lean_object* l_Lean_Fmt_fmtGrindShowCases___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowCases___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowCases___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowCases___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowCases___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowCases___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowCases___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindShowCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 129, 48, 5, 176, 175, 163, 129)}};
static const lean_object* l_Lean_Fmt_fmtGrindShowCases___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowCases___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowCases___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindShowCases"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 234, 169, 239, 223, 213, 65, 72)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindShowState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showState"};
static const lean_object* l_Lean_Fmt_fmtGrindShowState___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowState___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowState___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowState___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowState___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowState___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowState___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowState___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowState___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowState___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindShowState___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 80, 82, 248, 223, 67, 174, 140)}};
static const lean_object* l_Lean_Fmt_fmtGrindShowState___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowState___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowState___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindShowState"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 80, 216, 113, 136, 198, 224, 189)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindCasesTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "casesTrace"};
static const lean_object* l_Lean_Fmt_fmtGrindCasesTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindCasesTrace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindCasesTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 50, 184, 173, 128, 245, 159, 246)}};
static const lean_object* l_Lean_Fmt_fmtGrindCasesTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindCasesTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCasesTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCasesTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtGrindCasesTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 116, 148, 24, 99, 107, 176, 70)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindShowTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTerm"};
static const lean_object* l_Lean_Fmt_fmtGrindShowTerm___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowTerm___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTerm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowTerm___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTerm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowTerm___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTerm___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowTerm___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindShowTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindShowTerm___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindShowTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 150, 74, 14, 71, 142, 109, 156)}};
static const lean_object* l_Lean_Fmt_fmtGrindShowTerm___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindShowTerm___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowTerm___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindShowTerm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 67, 80, 76, 90, 73, 172, 250)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindTacticCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Lean_Fmt_fmtGrindTacticCases___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindTacticCases___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindTacticCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTacticCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTacticCases___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTacticCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTacticCases___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTacticCases___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTacticCases___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTacticCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTacticCases___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindTacticCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 233, 158, 17, 45, 135, 214, 137)}};
static const lean_object* l_Lean_Fmt_fmtGrindTacticCases___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindTacticCases___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTacticCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTacticCases___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindTacticCases"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 212, 160, 37, 58, 164, 216)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindWithAnnotateState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindWithAnnotateState___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withAnnotateState"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 242, 153, 188, 185, 49, 129, 186)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "fmtGrindWithAnnotateState"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(145, 187, 73, 103, 16, 95, 107, 7)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fail"};
static const lean_object* l_Lean_Fmt_fmtGrindFail___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFail___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFail___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFail___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFail___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFail___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 42, 125, 152, 218, 230, 194, 180)}};
static const lean_object* l_Lean_Fmt_fmtGrindFail___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindFail___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtGrindFail___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFail___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtGrindFail___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindFail___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFail___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGrindFail"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 7, 79, 114, 59, 36, 200, 145)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindRenameI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "renameI"};
static const lean_object* l_Lean_Fmt_fmtGrindRenameI___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindRenameI___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindRenameI___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRenameI___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRenameI___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRenameI___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRenameI___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRenameI___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRenameI___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRenameI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRenameI___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindRenameI___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 25, 204, 129, 223, 148, 21, 212)}};
static const lean_object* l_Lean_Fmt_fmtGrindRenameI___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindRenameI___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRenameI(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRenameI___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGrindRenameI"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 63, 62, 14, 147, 154, 151, 181)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symApply"};
static const lean_object* l_Lean_Fmt_fmtGrindApply___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindApply___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindApply___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindApply___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindApply___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindApply___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindApply___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindApply___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindApply___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindApply___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindApply___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindApply___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 244, 96, 104, 113, 83, 151, 74)}};
static const lean_object* l_Lean_Fmt_fmtGrindApply___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindApply___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindApply(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindApply___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindApply"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 221, 116, 230, 38, 223, 87, 251)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindInternalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "symInternalize"};
static const lean_object* l_Lean_Fmt_fmtGrindInternalize___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindInternalize___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindInternalize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindInternalize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindInternalize___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindInternalize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindInternalize___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindInternalize___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindInternalize___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindInternalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindInternalize___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindInternalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 99, 88, 106, 108, 255, 121, 14)}};
static const lean_object* l_Lean_Fmt_fmtGrindInternalize___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindInternalize___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindInternalize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindInternalize___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindInternalize"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 115, 31, 138, 92, 42, 46, 23)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindExact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindExact_"};
static const lean_object* l_Lean_Fmt_fmtGrindExact___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindExact___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindExact___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindExact___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindExact___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindExact___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindExact___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindExact___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindExact___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindExact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindExact___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 67, 233, 5, 161, 243, 203, 153)}};
static const lean_object* l_Lean_Fmt_fmtGrindExact___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindExact___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindExact(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindExact___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindExact"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 33, 70, 22, 67, 3, 137, 235)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindInstantiate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "instantiate"};
static const lean_object* l_Lean_Fmt_fmtGrindInstantiate___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindInstantiate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindInstantiate___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindInstantiate___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindInstantiate___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindInstantiate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 223, 197, 126, 28, 51, 106, 179)}};
static const lean_object* l_Lean_Fmt_fmtGrindInstantiate___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindInstantiate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtGrindInstantiate___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__2_value;
static const lean_array_object l_Lean_Fmt_fmtGrindInstantiate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtGrindInstantiate___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindInstantiate___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindInstantiate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindInstantiate___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindInstantiate"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 231, 108, 82, 163, 173, 245, 54)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "use"};
static const lean_object* l_Lean_Fmt_fmtGrindUse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindUse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindUse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindUse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindUse___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindUse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindUse___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindUse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindUse___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindUse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindUse___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindUse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 64, 35, 249, 247, 52, 171, 66)}};
static const lean_object* l_Lean_Fmt_fmtGrindUse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindUse___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindUse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindUse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindUse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 22, 247, 46, 21, 79, 1, 79)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFinish___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finish"};
static const lean_object* l_Lean_Fmt_fmtGrindFinish___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFinish___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinish___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinish___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFinish___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinish___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFinish___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinish___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFinish___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinish___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFinish___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFinish___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 141, 128, 132, 58, 161, 38, 215)}};
static const lean_object* l_Lean_Fmt_fmtGrindFinish___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFinish___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFinish(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFinish___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtGrindFinish"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 187, 123, 86, 201, 13, 255, 110)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFinishTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "finishTrace"};
static const lean_object* l_Lean_Fmt_fmtGrindFinishTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFinishTrace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFinishTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 104, 221, 59, 99, 114, 168, 144)}};
static const lean_object* l_Lean_Fmt_fmtGrindFinishTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFinishTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFinishTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFinishTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindFinishTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 218, 171, 168, 191, 209, 101, 179)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l_Lean_Fmt_fmtGrindHave___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 36, 229, 233, 71, 216, 202, 183)}};
static const lean_object* l_Lean_Fmt_fmtGrindHave___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtGrindHave___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindHave___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Fmt_fmtGrindHave___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHave___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Fmt_fmtGrindHave___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindHave___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHave(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHave___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGrindHave"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 130, 195, 137, 194, 134, 3, 189)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindHaveSilent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "haveSilent"};
static const lean_object* l_Lean_Fmt_fmtGrindHaveSilent___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindHaveSilent___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindHaveSilent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 40, 33, 99, 54, 221, 176, 65)}};
static const lean_object* l_Lean_Fmt_fmtGrindHaveSilent___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindHaveSilent___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtGrindHaveSilent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtGrindHaveSilent___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindHaveSilent___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHaveSilent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHaveSilent___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtGrindHaveSilent"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 191, 50, 201, 18, 135, 114, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nestedTacticCore"};
static const lean_object* l_Lean_Fmt_fmtGrindNestedTacticCore___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 148, 190, 235, 218, 2, 248, 160)}};
static const lean_object* l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Fmt_fmtGrindNestedTacticCore___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNestedTacticCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNestedTacticCore___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtGrindNestedTacticCore"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 64, 131, 61, 36, 154, 74, 25)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindAllGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Lean_Fmt_fmtGrindAllGoals___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindAllGoals___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindAllGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAllGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAllGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAllGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAllGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAllGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAllGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAllGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAllGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindAllGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 176, 42, 44, 172, 202, 38, 34)}};
static const lean_object* l_Lean_Fmt_fmtGrindAllGoals___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindAllGoals___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAllGoals(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAllGoals___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindAllGoals"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 192, 85, 2, 123, 66, 197, 74)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l_Lean_Fmt_fmtGrindCase___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindCase___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindCase___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCase___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCase___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCase___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCase___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCase___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCase___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCase___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindCase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 173, 21, 189, 81, 211, 125, 169)}};
static const lean_object* l_Lean_Fmt_fmtGrindCase___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindCase___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCase___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGrindCase"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 154, 30, 244, 134, 142, 255, 127)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindAnyGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "anyGoals"};
static const lean_object* l_Lean_Fmt_fmtGrindAnyGoals___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnyGoals___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindAnyGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 3, 10, 44, 226, 136, 80, 42)}};
static const lean_object* l_Lean_Fmt_fmtGrindAnyGoals___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnyGoals___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnyGoals(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnyGoals___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindAnyGoals"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 255, 18, 86, 113, 145, 133, 77)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFocus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "focus"};
static const lean_object* l_Lean_Fmt_fmtGrindFocus___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFocus___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFocus___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFocus___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFocus___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFocus___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFocus___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFocus___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFocus___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFocus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFocus___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFocus___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 68, 95, 128, 15, 244, 165, 139)}};
static const lean_object* l_Lean_Fmt_fmtGrindFocus___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFocus___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFocus(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFocus___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindFocus"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 170, 133, 142, 98, 178, 85, 223)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFailIfSuccess___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "failIfSuccess"};
static const lean_object* l_Lean_Fmt_fmtGrindFailIfSuccess___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFailIfSuccess___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFailIfSuccess___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 235, 219, 147, 187, 132, 195, 48)}};
static const lean_object* l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFailIfSuccess(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFailIfSuccess___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtGrindFailIfSuccess"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 170, 0, 63, 230, 119, 60, 174)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindTry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindTry_"};
static const lean_object* l_Lean_Fmt_fmtGrindTry___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindTry___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindTry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTry___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTry___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTry___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTry___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTry___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindTry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 12, 37, 83, 85, 34, 35, 178)}};
static const lean_object* l_Lean_Fmt_fmtGrindTry___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindTry___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindTry"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 168, 197, 68, 204, 5, 67, 38)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindRepeat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindRepeat_"};
static const lean_object* l_Lean_Fmt_fmtGrindRepeat___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindRepeat___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindRepeat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRepeat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRepeat___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRepeat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRepeat___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRepeat___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRepeat___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRepeat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRepeat___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 93, 145, 161, 123, 119, 39, 92)}};
static const lean_object* l_Lean_Fmt_fmtGrindRepeat___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindRepeat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRepeat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRepeat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtGrindRepeat"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 71, 108, 113, 108, 59, 36, 233)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindNext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l_Lean_Fmt_fmtGrindNext___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindNext___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindNext___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNext___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNext___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNext___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNext___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNext___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNext___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNext___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindNext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 67, 127, 148, 132, 17, 131, 108)}};
static const lean_object* l_Lean_Fmt_fmtGrindNext___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindNext___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNext___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGrindNext"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 6, 0, 31, 126, 105, 160, 127)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindDot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "grind·_"};
static const lean_object* l_Lean_Fmt_fmtGrindDot___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindDot___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindDot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDot___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDot___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDot___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDot___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindDot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 208, 22, 131, 194, 122, 241, 171)}};
static const lean_object* l_Lean_Fmt_fmtGrindDot___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindDot___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDot___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindDot"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 148, 160, 171, 239, 213, 235, 62)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeqFocus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtGrindSeqFocus___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeqFocus___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSeqFocus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSeqFocus___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtGrindSeqFocus___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSeqFocus___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtGrindSeqFocus___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtGrindSeqFocus___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtGrindSeqFocus___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtGrindSeqFocus___closed__3;
static lean_once_cell_t l_Lean_Fmt_fmtGrindSeqFocus___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtGrindSeqFocus___closed__4;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeqFocus;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_<;>_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 7, 229, 204, 205, 179, 221, 240)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindSeqFocus"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(147, 136, 231, 162, 17, 120, 200, 118)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindFirst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Fmt_fmtGrindFirst___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindFirst___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindFirst___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFirst___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFirst___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFirst___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFirst___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFirst___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFirst___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindFirst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindFirst___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindFirst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 60, 110, 192, 46, 198, 252, 25)}};
static const lean_object* l_Lean_Fmt_fmtGrindFirst___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindFirst___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFirst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFirst___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindFirst"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 13, 63, 12, 160, 99, 167, 129)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Fmt_fmtGrindParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindParen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindParen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindParen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindParen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindParen___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 134, 107, 245, 63, 193, 1, 88)}};
static const lean_object* l_Lean_Fmt_fmtGrindParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 31, 52, 187, 71, 239, 120, 146)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSetOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "setOption"};
static const lean_object* l_Lean_Fmt_fmtGrindSetOption___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSetOption___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetOption___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetOption___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSetOption___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetOption___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSetOption___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetOption___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSetOption___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSetOption___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSetOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 132, 183, 171, 34, 48, 139, 102)}};
static const lean_object* l_Lean_Fmt_fmtGrindSetOption___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSetOption___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGrindSetOption___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindSetOption___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSetOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSetOption___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindSetOption"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 152, 201, 146, 14, 228, 115, 81)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "setConfig"};
static const lean_object* l_Lean_Fmt_fmtGrindSetConfig___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSetConfig___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSetConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetConfig___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSetConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetConfig___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSetConfig___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSetConfig___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 24, 145, 44, 206, 52, 130, 57)}};
static const lean_object* l_Lean_Fmt_fmtGrindSetConfig___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSetConfig___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSetConfig___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindSetConfig"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 253, 83, 133, 14, 57, 16, 216)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSymIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symIntro"};
static const lean_object* l_Lean_Fmt_fmtGrindSymIntro___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSymIntro___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntro___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntro___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntro___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 177, 203, 220, 6, 189, 203, 250)}};
static const lean_object* l_Lean_Fmt_fmtGrindSymIntro___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSymIntro___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindSymIntro"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 200, 103, 159, 108, 231, 30, 72)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSymIntroLight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "symIntroLight"};
static const lean_object* l_Lean_Fmt_fmtGrindSymIntroLight___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSymIntroLight___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSymIntroLight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 188, 225, 186, 156, 62, 173, 87)}};
static const lean_object* l_Lean_Fmt_fmtGrindSymIntroLight___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSymIntroLight___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntroLight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntroLight___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtGrindSymIntroLight"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 83, 27, 88, 28, 175, 38, 82)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSymIntros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "symIntros"};
static const lean_object* l_Lean_Fmt_fmtGrindSymIntros___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSymIntros___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntros___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntros___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntros___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntros___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntros___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntros___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntros___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntros___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntros___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSymIntros___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 175, 114, 140, 112, 61, 143, 32)}};
static const lean_object* l_Lean_Fmt_fmtGrindSymIntros___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSymIntros___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntros(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntros___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindSymIntros"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 223, 193, 85, 120, 206, 60, 50)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSymIntrosLight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "symIntrosLight"};
static const lean_object* l_Lean_Fmt_fmtGrindSymIntrosLight___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSymIntrosLight___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSymIntrosLight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 124, 219, 142, 239, 75, 103, 85)}};
static const lean_object* l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntrosLight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntrosLight___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtGrindSymIntrosLight"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 74, 155, 54, 173, 250, 21, 87)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "symSimp"};
static const lean_object* l_Lean_Fmt_fmtGrindSimp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSimp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSimp___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSimp___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 109, 151, 25, 234, 136, 56, 252)}};
static const lean_object* l_Lean_Fmt_fmtGrindSimp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSimp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGrindSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 132, 84, 13, 221, 103, 163, 114)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDSimp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindDSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symDSimp"};
static const lean_object* l_Lean_Fmt_fmtGrindDSimp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindDSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDSimp___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 250, 158, 59, 57, 156, 255, 54)}};
static const lean_object* l_Lean_Fmt_fmtGrindDSimp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__1_value;
static const lean_closure_object l_Lean_Fmt_fmtGrindDSimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtGrindDSimp___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtGrindDSimp___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindDSimp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtStarOrIdent"};
static const lean_object* l_Lean_Fmt_fmtGrindDSimp___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindDSimp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 254, 13, 119, 139, 216, 202, 237)}};
static const lean_object* l_Lean_Fmt_fmtGrindDSimp___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindDSimp___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindDSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 111, 70, 68, 158, 126, 115, 46)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindRw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "symRw"};
static const lean_object* l_Lean_Fmt_fmtGrindRw___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 41, 80, 24, 116, 161, 83, 223)}};
static const lean_object* l_Lean_Fmt_fmtGrindRw___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindRw___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l_Lean_Fmt_fmtGrindRw___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindRw___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__2_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l_Lean_Fmt_fmtGrindRw___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindRw___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRw___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtGrindRw"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 1, 22, 103, 191, 65, 217, 129)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindBvNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Fmt_fmtGrindBvNormalize___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 136, 123, 235, 182, 158, 80)}};
static const lean_object* l_Lean_Fmt_fmtGrindBvNormalize___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindBvNormalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Fmt_fmtGrindBvNormalize___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Fmt_fmtGrindBvNormalize___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtGrindBvNormalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTypes"};
static const lean_object* l_Lean_Fmt_fmtGrindBvNormalize___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvNormalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__4_value),LEAN_SCALAR_PTR_LITERAL(133, 159, 97, 61, 240, 205, 127, 31)}};
static const lean_object* l_Lean_Fmt_fmtGrindBvNormalize___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvNormalize___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvNormalize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvNormalize___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindBvNormalize"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 155, 171, 134, 91, 156, 37, 140)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindBvDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bvDecide"};
static const lean_object* l_Lean_Fmt_fmtGrindBvDecide___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvDecide___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecide___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecide___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvDecide___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecide___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvDecide___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecide___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvDecide___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvDecide___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 150, 103, 35, 70, 25, 10, 148)}};
static const lean_object* l_Lean_Fmt_fmtGrindBvDecide___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvDecide___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvDecide(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvDecide___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindBvDecide"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 29, 112, 14, 102, 146, 177, 37)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindBvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l_Lean_Fmt_fmtGrindBvTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvTrace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 142, 92, 236, 193, 5, 157, 115)}};
static const lean_object* l_Lean_Fmt_fmtGrindBvTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGrindBvTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 201, 215, 72, 55, 64, 87, 52)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindBvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Fmt_fmtGrindBvCheck___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvCheck___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvCheck___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvCheck___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvCheck___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvCheck___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvCheck___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvCheck___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvCheck___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvCheck___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 89, 115, 113, 62, 113, 141, 105)}};
static const lean_object* l_Lean_Fmt_fmtGrindBvCheck___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvCheck___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvCheck(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvCheck___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGrindBvCheck"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 98, 157, 25, 21, 203, 5, 46)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindBvDecidePush___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bvDecidePush"};
static const lean_object* l_Lean_Fmt_fmtGrindBvDecidePush___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvDecidePush___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindThmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindBvDecidePush___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 198, 224, 172, 164, 17, 35, 6)}};
static const lean_object* l_Lean_Fmt_fmtGrindBvDecidePush___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindBvDecidePush___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvDecidePush(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvDecidePush___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtGrindBvDecidePush"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 62, 143, 233, 177, 158, 198, 198)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnchor(lean_object* v_x_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnchor___closed__4));
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
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_13_, v___x_20_);
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnchor___closed__6));
lean_inc(v___x_21_);
v___x_23_ = l_Lean_Syntax_isOfKind(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v___x_21_);
lean_dec(v_x_13_);
v___x_24_ = l_Lean_Fmt_Error_partialFormatter;
v___x_25_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v_a_15_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v_hashTk_27_; lean_object* v___x_28_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v_hashTk_27_ = l_Lean_Syntax_getArg(v_x_13_, v___x_26_);
lean_dec(v_x_13_);
v___x_28_ = l_Lean_Fmt_fmt(v_hashTk_27_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_31_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
lean_inc(v_a_30_);
lean_dec_ref_known(v___x_28_, 2);
v___x_31_ = l_Lean_Fmt_fmt(v___x_21_, v_a_14_, v_a_30_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_45_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_45_ == 0)
{
v___x_35_ = v___x_31_;
v_isShared_36_ = v_isSharedCheck_45_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_45_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_37_ = lean_unsigned_to_nat(2u);
v___x_38_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_39_ = lean_array_push(v___x_38_, v_a_29_);
v___x_40_ = lean_array_push(v___x_39_, v_a_32_);
v___x_41_ = l_Lean_Fmt_Layouts_atomic(v___x_40_);
lean_dec_ref(v___x_40_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_41_);
v___x_43_ = v___x_35_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_a_33_);
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
lean_dec(v_a_29_);
return v___x_31_;
}
}
else
{
lean_dec(v___x_21_);
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnchor___boxed(lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Fmt_fmtGrindAnchor(v_x_46_, v_a_47_, v_a_48_);
lean_dec_ref(v_a_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_57_ = l_Lean_Fmt_fmtAttribute;
v___x_58_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnchor___closed__4));
v___x_59_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___closed__2));
v___x_60_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindAnchor___boxed), 3, 0);
v___x_61_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_57_, v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1___boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLemma(lean_object* v_x_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v_mod_x3f_108_; lean_object* v___y_109_; lean_object* v___y_110_; 
v___x_80_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLemma___closed__1));
lean_inc(v_x_77_);
v___x_81_ = l_Lean_Syntax_isOfKind(v_x_77_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_x_77_);
v___x_122_ = l_Lean_Fmt_Error_partialFormatter;
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_a_79_);
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_Lean_Syntax_getArg(v_x_77_, v___x_124_);
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
lean_dec(v_x_77_);
v___x_129_ = l_Lean_Fmt_Error_partialFormatter;
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v_a_79_);
return v___x_130_;
}
else
{
lean_object* v_mod_x3f_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_mod_x3f_131_ = l_Lean_Syntax_getArg(v___x_125_, v___x_124_);
lean_dec(v___x_125_);
v___x_132_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLemma___closed__4));
lean_inc(v_mod_x3f_131_);
v___x_133_ = l_Lean_Syntax_isOfKind(v_mod_x3f_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_mod_x3f_131_);
lean_dec(v_x_77_);
v___x_134_ = l_Lean_Fmt_Error_partialFormatter;
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_79_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v_mod_x3f_131_);
v_mod_x3f_108_ = v___x_136_;
v___y_109_ = v_a_78_;
v___y_110_ = v_a_79_;
goto v___jp_107_;
}
}
}
else
{
lean_object* v___x_137_; 
lean_dec(v___x_125_);
v___x_137_ = lean_box(0);
v_mod_x3f_108_ = v___x_137_;
v___y_109_ = v_a_78_;
v___y_110_ = v_a_79_;
goto v___jp_107_;
}
}
v___jp_82_:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Fmt_fmt_x3f(v___y_86_, v___y_84_, v___y_83_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v_a_89_; lean_object* v___x_90_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
v_a_89_ = lean_ctor_get(v___x_87_, 1);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_87_, 2);
v___x_90_ = l_Lean_Fmt_fmt(v___y_85_, v___y_84_, v_a_89_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_106_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_a_92_ = lean_ctor_get(v___x_90_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_106_ == 0)
{
v___x_94_ = v___x_90_;
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_106_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_96_ = lean_unsigned_to_nat(2u);
v___x_97_ = lean_mk_empty_array_with_capacity(v___x_96_);
v___x_98_ = lean_array_push(v___x_97_, v_a_88_);
v___x_99_ = lean_array_push(v___x_98_, v_a_91_);
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_101_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_101_, 1, v___x_100_);
lean_ctor_set_uint8(v___x_101_, 2, v___x_100_);
lean_ctor_set_uint8(v___x_101_, 3, v___x_100_);
v___x_102_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_99_, v___x_101_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_102_);
v___x_104_ = v___x_94_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_a_92_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
lean_dec(v_a_88_);
return v___x_90_;
}
}
else
{
lean_dec(v___y_85_);
return v___x_87_;
}
}
v___jp_107_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = l_Lean_Syntax_getArg(v_x_77_, v___x_111_);
lean_dec(v_x_77_);
if (lean_obj_tag(v_mod_x3f_108_) == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(0);
v___y_83_ = v___y_110_;
v___y_84_ = v___y_109_;
v___y_85_ = v___x_112_;
v___y_86_ = v___x_113_;
goto v___jp_82_;
}
else
{
lean_object* v_val_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_val_114_ = lean_ctor_get(v_mod_x3f_108_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v_mod_x3f_108_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v_mod_x3f_108_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_val_114_);
lean_dec(v_mod_x3f_108_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_val_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v___y_83_ = v___y_110_;
v___y_84_ = v___y_109_;
v___y_85_ = v___x_112_;
v___y_86_ = v___x_119_;
goto v___jp_82_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLemma___boxed(lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Fmt_fmtGrindLemma(v_x_138_, v_a_139_, v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1(){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_148_ = l_Lean_Fmt_fmtAttribute;
v___x_149_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLemma___closed__1));
v___x_150_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___closed__1));
v___x_151_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindLemma___boxed), 3, 0);
v___x_152_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_148_, v___x_149_, v___x_150_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1___boxed(lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1();
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLemmaMin(lean_object* v_x_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; 
v___x_164_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLemmaMin___closed__1));
lean_inc(v_x_161_);
v___x_165_ = l_Lean_Syntax_isOfKind(v_x_161_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_x_161_);
v___x_194_ = l_Lean_Fmt_Error_partialFormatter;
v___x_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_163_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v_bangTk_197_; lean_object* v_mod_x3f_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v_bangTk_197_ = l_Lean_Syntax_getArg(v_x_161_, v___x_196_);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = l_Lean_Syntax_getArg(v_x_161_, v___x_216_);
v___x_218_ = l_Lean_Syntax_isNone(v___x_217_);
if (v___x_218_ == 0)
{
uint8_t v___x_219_; 
lean_inc(v___x_217_);
v___x_219_ = l_Lean_Syntax_matchesNull(v___x_217_, v___x_216_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v___x_217_);
lean_dec(v_bangTk_197_);
lean_dec(v_x_161_);
v___x_220_ = l_Lean_Fmt_Error_partialFormatter;
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_163_);
return v___x_221_;
}
else
{
lean_object* v_mod_x3f_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_mod_x3f_222_ = l_Lean_Syntax_getArg(v___x_217_, v___x_196_);
lean_dec(v___x_217_);
v___x_223_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLemma___closed__4));
lean_inc(v_mod_x3f_222_);
v___x_224_ = l_Lean_Syntax_isOfKind(v_mod_x3f_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_mod_x3f_222_);
lean_dec(v_bangTk_197_);
lean_dec(v_x_161_);
v___x_225_ = l_Lean_Fmt_Error_partialFormatter;
v___x_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_a_163_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_mod_x3f_222_);
v_mod_x3f_199_ = v___x_227_;
v___y_200_ = v_a_162_;
v___y_201_ = v_a_163_;
goto v___jp_198_;
}
}
}
else
{
lean_object* v___x_228_; 
lean_dec(v___x_217_);
v___x_228_ = lean_box(0);
v_mod_x3f_199_ = v___x_228_;
v___y_200_ = v_a_162_;
v___y_201_ = v_a_163_;
goto v___jp_198_;
}
v___jp_198_:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Fmt_fmt(v_bangTk_197_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_a_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
v_a_204_ = lean_ctor_get(v___x_202_, 1);
lean_inc(v_a_204_);
lean_dec_ref_known(v___x_202_, 2);
v___x_205_ = lean_unsigned_to_nat(2u);
v___x_206_ = l_Lean_Syntax_getArg(v_x_161_, v___x_205_);
lean_dec(v_x_161_);
if (lean_obj_tag(v_mod_x3f_199_) == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
v___y_167_ = v___x_205_;
v___y_168_ = v___x_206_;
v___y_169_ = v_a_203_;
v___y_170_ = v_a_204_;
v___y_171_ = v___y_200_;
v___y_172_ = v___x_207_;
goto v___jp_166_;
}
else
{
lean_object* v_val_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_val_208_ = lean_ctor_get(v_mod_x3f_199_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v_mod_x3f_199_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v_mod_x3f_199_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_val_208_);
lean_dec(v_mod_x3f_199_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_val_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v___y_167_ = v___x_205_;
v___y_168_ = v___x_206_;
v___y_169_ = v_a_203_;
v___y_170_ = v_a_204_;
v___y_171_ = v___y_200_;
v___y_172_ = v___x_213_;
goto v___jp_166_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_199_);
lean_dec(v_x_161_);
return v___x_202_;
}
}
}
v___jp_166_:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Fmt_fmt_x3f(v___y_172_, v___y_171_, v___y_170_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
v_a_175_ = lean_ctor_get(v___x_173_, 1);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_173_, 2);
v___x_176_ = l_Lean_Fmt_fmt(v___y_168_, v___y_171_, v_a_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_193_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_a_178_ = lean_ctor_get(v___x_176_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_193_ == 0)
{
v___x_180_ = v___x_176_;
v_isShared_181_ = v_isSharedCheck_193_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_193_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_182_ = lean_mk_empty_array_with_capacity(v___y_167_);
v___x_183_ = lean_array_push(v___x_182_, v_a_174_);
v___x_184_ = lean_array_push(v___x_183_, v_a_177_);
v___x_185_ = 0;
v___x_186_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_186_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_186_, 1, v___x_185_);
lean_ctor_set_uint8(v___x_186_, 2, v___x_185_);
lean_ctor_set_uint8(v___x_186_, 3, v___x_185_);
v___x_187_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_184_, v___x_186_);
v___x_188_ = 1;
v___x_189_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_169_, v___x_187_, v___x_188_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_189_);
v___x_191_ = v___x_180_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_a_178_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
else
{
lean_dec(v_a_174_);
lean_dec_ref(v___y_169_);
return v___x_176_;
}
}
else
{
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLemmaMin___boxed(lean_object* v_x_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Fmt_fmtGrindLemmaMin(v_x_229_, v_a_230_, v_a_231_);
lean_dec_ref(v_a_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1(){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_239_ = l_Lean_Fmt_fmtAttribute;
v___x_240_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLemmaMin___closed__1));
v___x_241_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___closed__1));
v___x_242_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindLemmaMin___boxed), 3, 0);
v___x_243_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_239_, v___x_240_, v___x_241_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1___boxed(lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1();
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindErase(lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__1));
lean_inc(v_x_255_);
v___x_259_ = l_Lean_Syntax_isOfKind(v_x_255_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_x_255_);
v___x_260_ = l_Lean_Fmt_Error_partialFormatter;
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = l_Lean_Syntax_getArg(v_x_255_, v___x_262_);
v___x_264_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__3));
lean_inc(v___x_263_);
v___x_265_ = l_Lean_Syntax_isOfKind(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v___x_263_);
lean_dec(v_x_255_);
v___x_266_ = l_Lean_Fmt_Error_partialFormatter;
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_a_257_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v_minusTk_269_; lean_object* v___x_270_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v_minusTk_269_ = l_Lean_Syntax_getArg(v_x_255_, v___x_268_);
lean_dec(v_x_255_);
v___x_270_ = l_Lean_Fmt_fmt(v_minusTk_269_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_a_272_; lean_object* v___x_273_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
v_a_272_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_270_, 2);
v___x_273_ = l_Lean_Fmt_fmt(v___x_263_, v_a_256_, v_a_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_287_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_a_275_ = lean_ctor_get(v___x_273_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_287_ == 0)
{
v___x_277_ = v___x_273_;
v_isShared_278_ = v_isSharedCheck_287_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_287_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_279_ = lean_unsigned_to_nat(2u);
v___x_280_ = lean_mk_empty_array_with_capacity(v___x_279_);
v___x_281_ = lean_array_push(v___x_280_, v_a_271_);
v___x_282_ = lean_array_push(v___x_281_, v_a_274_);
v___x_283_ = l_Lean_Fmt_Layouts_atomic(v___x_282_);
lean_dec_ref(v___x_282_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_283_);
v___x_285_ = v___x_277_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_a_275_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
else
{
lean_dec(v_a_271_);
return v___x_273_;
}
}
else
{
lean_dec(v___x_263_);
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindErase___boxed(lean_object* v_x_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Fmt_fmtGrindErase(v_x_288_, v_a_289_, v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1(){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_298_ = l_Lean_Fmt_fmtAttribute;
v___x_299_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__1));
v___x_300_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___closed__1));
v___x_301_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindErase___boxed), 3, 0);
v___x_302_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_298_, v___x_299_, v___x_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1___boxed(lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindParam(lean_object* v_stx_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_305_, v___x_308_, v_a_307_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
v_a_311_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_309_, 2);
v___x_312_ = l_Lean_Fmt_fmt(v_a_310_, v_a_306_, v_a_311_);
return v___x_312_;
}
else
{
lean_object* v_a_313_; lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_313_ = lean_ctor_get(v___x_309_, 0);
v_a_314_ = lean_ctor_get(v___x_309_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_309_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_inc(v_a_313_);
lean_dec(v___x_309_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_313_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindParam___boxed(lean_object* v_stx_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Fmt_fmtGrindParam(v_stx_322_, v_a_323_, v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_stx_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1(){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_338_ = l_Lean_Fmt_fmtAttribute;
v___x_339_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__1));
v___x_340_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___closed__3));
v___x_341_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindParam___boxed), 3, 0);
v___x_342_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_338_, v___x_339_, v___x_340_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1___boxed(lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1();
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindThmNs(lean_object* v_x_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Fmt_fmtGrindThmNs___closed__2));
lean_inc(v_x_353_);
v___x_357_ = l_Lean_Syntax_isOfKind(v_x_353_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_x_353_);
v___x_358_ = l_Lean_Fmt_Error_partialFormatter;
v___x_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v_a_355_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = l_Lean_Syntax_getArg(v_x_353_, v___x_360_);
v___x_362_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__3));
lean_inc(v___x_361_);
v___x_363_ = l_Lean_Syntax_isOfKind(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v___x_361_);
lean_dec(v_x_353_);
v___x_364_ = l_Lean_Fmt_Error_partialFormatter;
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_a_355_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; lean_object* v_nsTk_367_; lean_object* v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v_nsTk_367_ = l_Lean_Syntax_getArg(v_x_353_, v___x_366_);
lean_dec(v_x_353_);
v___x_368_ = l_Lean_Fmt_fmt(v_nsTk_367_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v_a_370_; lean_object* v___x_371_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
v_a_370_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_368_, 2);
v___x_371_ = l_Lean_Fmt_fmt(v___x_361_, v_a_354_, v_a_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_387_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_a_373_ = lean_ctor_get(v___x_371_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_387_ == 0)
{
v___x_375_ = v___x_371_;
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_377_ = lean_unsigned_to_nat(2u);
v___x_378_ = lean_mk_empty_array_with_capacity(v___x_377_);
v___x_379_ = lean_array_push(v___x_378_, v_a_369_);
v___x_380_ = lean_array_push(v___x_379_, v_a_372_);
v___x_381_ = 0;
v___x_382_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_382_, 0, v___x_363_);
lean_ctor_set_uint8(v___x_382_, 1, v___x_381_);
lean_ctor_set_uint8(v___x_382_, 2, v___x_381_);
lean_ctor_set_uint8(v___x_382_, 3, v___x_381_);
v___x_383_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_380_, v___x_382_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_383_);
v___x_385_ = v___x_375_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_a_373_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_dec(v_a_369_);
return v___x_371_;
}
}
else
{
lean_dec(v___x_361_);
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindThmNs___boxed(lean_object* v_x_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Fmt_fmtGrindThmNs(v_x_388_, v_a_389_, v_a_390_);
lean_dec_ref(v_a_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1(){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_398_ = l_Lean_Fmt_fmtAttribute;
v___x_399_ = ((lean_object*)(l_Lean_Fmt_fmtGrindThmNs___closed__2));
v___x_400_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___closed__1));
v___x_401_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindThmNs___boxed), 3, 0);
v___x_402_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_398_, v___x_399_, v___x_400_, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1___boxed(lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1();
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindThm(lean_object* v_stx_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_405_, v___x_408_, v_a_407_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v_a_411_; lean_object* v___x_412_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
v_a_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_409_, 2);
v___x_412_ = l_Lean_Fmt_fmt(v_a_410_, v_a_406_, v_a_411_);
return v___x_412_;
}
else
{
lean_object* v_a_413_; lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_a_413_ = lean_ctor_get(v___x_409_, 0);
v_a_414_ = lean_ctor_get(v___x_409_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_409_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_inc(v_a_413_);
lean_dec(v___x_409_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_413_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindThm___boxed(lean_object* v_stx_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Fmt_fmtGrindThm(v_stx_422_, v_a_423_, v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_stx_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1(){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_439_ = l_Lean_Fmt_fmtAttribute;
v___x_440_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__1));
v___x_441_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___closed__3));
v___x_442_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindThm___boxed), 3, 0);
v___x_443_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_439_, v___x_440_, v___x_441_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1___boxed(lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1();
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterIdent(lean_object* v_x_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterIdent___closed__1));
lean_inc(v_x_453_);
v___x_457_ = l_Lean_Syntax_isOfKind(v_x_453_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v_x_453_);
v___x_458_ = l_Lean_Fmt_Error_partialFormatter;
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_a_455_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = l_Lean_Syntax_getArg(v_x_453_, v___x_460_);
lean_dec(v_x_453_);
v___x_462_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__3));
lean_inc(v___x_461_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v___x_461_);
v___x_464_ = l_Lean_Fmt_Error_partialFormatter;
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_a_455_);
return v___x_465_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Fmt_fmt(v___x_461_, v_a_454_, v_a_455_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterIdent___boxed(lean_object* v_x_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Fmt_fmtGrindFilterIdent(v_x_467_, v_a_468_, v_a_469_);
lean_dec_ref(v_a_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1(){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_477_ = l_Lean_Fmt_fmtAttribute;
v___x_478_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterIdent___closed__1));
v___x_479_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___closed__1));
v___x_480_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterIdent___boxed), 3, 0);
v___x_481_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_477_, v___x_478_, v___x_479_, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1___boxed(lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1();
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenCmp(lean_object* v_genTk_487_, lean_object* v_opTk_488_, lean_object* v_n_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Fmt_fmt(v_genTk_487_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v_a_494_; lean_object* v___x_495_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
v_a_494_ = lean_ctor_get(v___x_492_, 1);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_492_, 2);
v___x_495_ = l_Lean_Fmt_fmt(v_opTk_488_, v_a_490_, v_a_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v_a_497_; lean_object* v___x_498_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
v_a_497_ = lean_ctor_get(v___x_495_, 1);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_495_, 2);
v___x_498_ = l_Lean_Fmt_fmt(v_n_489_, v_a_490_, v_a_497_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_514_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_a_500_ = lean_ctor_get(v___x_498_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_514_ == 0)
{
v___x_502_ = v___x_498_;
v_isShared_503_ = v_isSharedCheck_514_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_514_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_504_ = lean_unsigned_to_nat(3u);
v___x_505_ = lean_mk_empty_array_with_capacity(v___x_504_);
v___x_506_ = lean_array_push(v___x_505_, v_a_493_);
v___x_507_ = lean_array_push(v___x_506_, v_a_496_);
v___x_508_ = lean_array_push(v___x_507_, v_a_499_);
v___x_509_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenCmp___closed__0));
v___x_510_ = l_Lean_Fmt_Layouts_infixOperator(v___x_508_, v___x_509_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_510_);
v___x_512_ = v___x_502_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_a_500_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_dec(v_a_496_);
lean_dec(v_a_493_);
return v___x_498_;
}
}
else
{
lean_dec(v_a_493_);
lean_dec(v_n_489_);
return v___x_495_;
}
}
else
{
lean_dec(v_n_489_);
lean_dec(v_opTk_488_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenCmp___boxed(lean_object* v_genTk_515_, lean_object* v_opTk_516_, lean_object* v_n_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_515_, v_opTk_516_, v_n_517_, v_a_518_, v_a_519_);
lean_dec_ref(v_a_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLt(lean_object* v_x_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__1));
lean_inc(v_x_531_);
v___x_535_ = l_Lean_Syntax_isOfKind(v_x_531_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_x_531_);
v___x_536_ = l_Lean_Fmt_Error_partialFormatter;
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_a_533_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v_n_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_538_ = lean_unsigned_to_nat(2u);
v_n_539_ = l_Lean_Syntax_getArg(v_x_531_, v___x_538_);
v___x_540_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_539_);
v___x_541_ = l_Lean_Syntax_isOfKind(v_n_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v_n_539_);
lean_dec(v_x_531_);
v___x_542_ = l_Lean_Fmt_Error_partialFormatter;
v___x_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v_a_533_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; lean_object* v_genTk_545_; lean_object* v___x_546_; lean_object* v_opTk_547_; lean_object* v___x_548_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v_genTk_545_ = l_Lean_Syntax_getArg(v_x_531_, v___x_544_);
v___x_546_ = lean_unsigned_to_nat(1u);
v_opTk_547_ = l_Lean_Syntax_getArg(v_x_531_, v___x_546_);
lean_dec(v_x_531_);
v___x_548_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_545_, v_opTk_547_, v_n_539_, v_a_532_, v_a_533_);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLt___boxed(lean_object* v_x_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Fmt_fmtGrindFilterGenLt(v_x_549_, v_a_550_, v_a_551_);
lean_dec_ref(v_a_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1(){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_559_ = l_Lean_Fmt_fmtAttribute;
v___x_560_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__1));
v___x_561_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___closed__1));
v___x_562_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterGenLt___boxed), 3, 0);
v___x_563_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_559_, v___x_560_, v___x_561_, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1___boxed(lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1();
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenEq(lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenEq___closed__1));
lean_inc(v_x_573_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_x_573_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_x_573_);
v___x_578_ = l_Lean_Fmt_Error_partialFormatter;
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_a_575_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v_n_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_580_ = lean_unsigned_to_nat(2u);
v_n_581_ = l_Lean_Syntax_getArg(v_x_573_, v___x_580_);
v___x_582_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_581_);
v___x_583_ = l_Lean_Syntax_isOfKind(v_n_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_n_581_);
lean_dec(v_x_573_);
v___x_584_ = l_Lean_Fmt_Error_partialFormatter;
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_a_575_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v_genTk_587_; lean_object* v___x_588_; lean_object* v_opTk_589_; lean_object* v___x_590_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v_genTk_587_ = l_Lean_Syntax_getArg(v_x_573_, v___x_586_);
v___x_588_ = lean_unsigned_to_nat(1u);
v_opTk_589_ = l_Lean_Syntax_getArg(v_x_573_, v___x_588_);
lean_dec(v_x_573_);
v___x_590_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_587_, v_opTk_589_, v_n_581_, v_a_574_, v_a_575_);
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenEq___boxed(lean_object* v_x_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Fmt_fmtGrindFilterGenEq(v_x_591_, v_a_592_, v_a_593_);
lean_dec_ref(v_a_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1(){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_601_ = l_Lean_Fmt_fmtAttribute;
v___x_602_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenEq___closed__1));
v___x_603_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___closed__1));
v___x_604_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterGenEq___boxed), 3, 0);
v___x_605_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_601_, v___x_602_, v___x_603_, v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1___boxed(lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1();
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenNe(lean_object* v_x_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenNe___closed__1));
lean_inc(v_x_615_);
v___x_619_ = l_Lean_Syntax_isOfKind(v_x_615_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_x_615_);
v___x_620_ = l_Lean_Fmt_Error_partialFormatter;
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v_a_617_);
return v___x_621_;
}
else
{
lean_object* v___x_622_; lean_object* v_n_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_622_ = lean_unsigned_to_nat(2u);
v_n_623_ = l_Lean_Syntax_getArg(v_x_615_, v___x_622_);
v___x_624_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_623_);
v___x_625_ = l_Lean_Syntax_isOfKind(v_n_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec(v_n_623_);
lean_dec(v_x_615_);
v___x_626_ = l_Lean_Fmt_Error_partialFormatter;
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_a_617_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v_genTk_629_; lean_object* v___x_630_; lean_object* v_opTk_631_; lean_object* v___x_632_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v_genTk_629_ = l_Lean_Syntax_getArg(v_x_615_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(1u);
v_opTk_631_ = l_Lean_Syntax_getArg(v_x_615_, v___x_630_);
lean_dec(v_x_615_);
v___x_632_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_629_, v_opTk_631_, v_n_623_, v_a_616_, v_a_617_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenNe___boxed(lean_object* v_x_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Fmt_fmtGrindFilterGenNe(v_x_633_, v_a_634_, v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1(){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_643_ = l_Lean_Fmt_fmtAttribute;
v___x_644_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenNe___closed__1));
v___x_645_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___closed__1));
v___x_646_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterGenNe___boxed), 3, 0);
v___x_647_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_643_, v___x_644_, v___x_645_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1___boxed(lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1();
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLe(lean_object* v_x_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLe___closed__1));
lean_inc(v_x_657_);
v___x_661_ = l_Lean_Syntax_isOfKind(v_x_657_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_x_657_);
v___x_662_ = l_Lean_Fmt_Error_partialFormatter;
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_a_659_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v_n_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_664_ = lean_unsigned_to_nat(2u);
v_n_665_ = l_Lean_Syntax_getArg(v_x_657_, v___x_664_);
v___x_666_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_665_);
v___x_667_ = l_Lean_Syntax_isOfKind(v_n_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec(v_n_665_);
lean_dec(v_x_657_);
v___x_668_ = l_Lean_Fmt_Error_partialFormatter;
v___x_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v_a_659_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; lean_object* v_genTk_671_; lean_object* v___x_672_; lean_object* v_opTk_673_; lean_object* v___x_674_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v_genTk_671_ = l_Lean_Syntax_getArg(v_x_657_, v___x_670_);
v___x_672_ = lean_unsigned_to_nat(1u);
v_opTk_673_ = l_Lean_Syntax_getArg(v_x_657_, v___x_672_);
lean_dec(v_x_657_);
v___x_674_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_671_, v_opTk_673_, v_n_665_, v_a_658_, v_a_659_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLe___boxed(lean_object* v_x_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Fmt_fmtGrindFilterGenLe(v_x_675_, v_a_676_, v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1(){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_685_ = l_Lean_Fmt_fmtAttribute;
v___x_686_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLe___closed__1));
v___x_687_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___closed__1));
v___x_688_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterGenLe___boxed), 3, 0);
v___x_689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_685_, v___x_686_, v___x_687_, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1___boxed(lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1();
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLeAscii(lean_object* v_x_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1));
lean_inc(v_x_699_);
v___x_703_ = l_Lean_Syntax_isOfKind(v_x_699_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_x_699_);
v___x_704_ = l_Lean_Fmt_Error_partialFormatter;
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_a_701_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; lean_object* v_n_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_706_ = lean_unsigned_to_nat(2u);
v_n_707_ = l_Lean_Syntax_getArg(v_x_699_, v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_707_);
v___x_709_ = l_Lean_Syntax_isOfKind(v_n_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v_n_707_);
lean_dec(v_x_699_);
v___x_710_ = l_Lean_Fmt_Error_partialFormatter;
v___x_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_a_701_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; lean_object* v_genTk_713_; lean_object* v___x_714_; lean_object* v_opTk_715_; lean_object* v___x_716_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v_genTk_713_ = l_Lean_Syntax_getArg(v_x_699_, v___x_712_);
v___x_714_ = lean_unsigned_to_nat(1u);
v_opTk_715_ = l_Lean_Syntax_getArg(v_x_699_, v___x_714_);
lean_dec(v_x_699_);
v___x_716_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_713_, v_opTk_715_, v_n_707_, v_a_700_, v_a_701_);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenLeAscii___boxed(lean_object* v_x_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Fmt_fmtGrindFilterGenLeAscii(v_x_717_, v_a_718_, v_a_719_);
lean_dec_ref(v_a_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1(){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_727_ = l_Lean_Fmt_fmtAttribute;
v___x_728_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLeAscii___closed__1));
v___x_729_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___closed__1));
v___x_730_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterGenLeAscii___boxed), 3, 0);
v___x_731_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_727_, v___x_728_, v___x_729_, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1___boxed(lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1();
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGt(lean_object* v_x_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenGt___closed__1));
lean_inc(v_x_741_);
v___x_745_ = l_Lean_Syntax_isOfKind(v_x_741_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_x_741_);
v___x_746_ = l_Lean_Fmt_Error_partialFormatter;
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_a_743_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v_n_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_748_ = lean_unsigned_to_nat(2u);
v_n_749_ = l_Lean_Syntax_getArg(v_x_741_, v___x_748_);
v___x_750_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_749_);
v___x_751_ = l_Lean_Syntax_isOfKind(v_n_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v_n_749_);
lean_dec(v_x_741_);
v___x_752_ = l_Lean_Fmt_Error_partialFormatter;
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_a_743_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v_genTk_755_; lean_object* v___x_756_; lean_object* v_opTk_757_; lean_object* v___x_758_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v_genTk_755_ = l_Lean_Syntax_getArg(v_x_741_, v___x_754_);
v___x_756_ = lean_unsigned_to_nat(1u);
v_opTk_757_ = l_Lean_Syntax_getArg(v_x_741_, v___x_756_);
lean_dec(v_x_741_);
v___x_758_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_755_, v_opTk_757_, v_n_749_, v_a_742_, v_a_743_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGt___boxed(lean_object* v_x_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Fmt_fmtGrindFilterGenGt(v_x_759_, v_a_760_, v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1(){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_769_ = l_Lean_Fmt_fmtAttribute;
v___x_770_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenGt___closed__1));
v___x_771_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___closed__1));
v___x_772_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterGenGt___boxed), 3, 0);
v___x_773_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_769_, v___x_770_, v___x_771_, v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1___boxed(lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1();
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGe(lean_object* v_x_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenGe___closed__1));
lean_inc(v_x_783_);
v___x_787_ = l_Lean_Syntax_isOfKind(v_x_783_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec(v_x_783_);
v___x_788_ = l_Lean_Fmt_Error_partialFormatter;
v___x_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v_a_785_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; lean_object* v_n_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_790_ = lean_unsigned_to_nat(2u);
v_n_791_ = l_Lean_Syntax_getArg(v_x_783_, v___x_790_);
v___x_792_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_791_);
v___x_793_ = l_Lean_Syntax_isOfKind(v_n_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v_n_791_);
lean_dec(v_x_783_);
v___x_794_ = l_Lean_Fmt_Error_partialFormatter;
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v_a_785_);
return v___x_795_;
}
else
{
lean_object* v___x_796_; lean_object* v_genTk_797_; lean_object* v___x_798_; lean_object* v_opTk_799_; lean_object* v___x_800_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v_genTk_797_ = l_Lean_Syntax_getArg(v_x_783_, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(1u);
v_opTk_799_ = l_Lean_Syntax_getArg(v_x_783_, v___x_798_);
lean_dec(v_x_783_);
v___x_800_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_797_, v_opTk_799_, v_n_791_, v_a_784_, v_a_785_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGe___boxed(lean_object* v_x_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Fmt_fmtGrindFilterGenGe(v_x_801_, v_a_802_, v_a_803_);
lean_dec_ref(v_a_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1(){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_811_ = l_Lean_Fmt_fmtAttribute;
v___x_812_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenGe___closed__1));
v___x_813_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___closed__1));
v___x_814_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterGenGe___boxed), 3, 0);
v___x_815_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_811_, v___x_812_, v___x_813_, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1___boxed(lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1();
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGeAscii(lean_object* v_x_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1));
lean_inc(v_x_825_);
v___x_829_ = l_Lean_Syntax_isOfKind(v_x_825_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v_x_825_);
v___x_830_ = l_Lean_Fmt_Error_partialFormatter;
v___x_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_a_827_);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v_n_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_832_ = lean_unsigned_to_nat(2u);
v_n_833_ = l_Lean_Syntax_getArg(v_x_825_, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_833_);
v___x_835_ = l_Lean_Syntax_isOfKind(v_n_833_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_n_833_);
lean_dec(v_x_825_);
v___x_836_ = l_Lean_Fmt_Error_partialFormatter;
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v_a_827_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v_genTk_839_; lean_object* v___x_840_; lean_object* v_opTk_841_; lean_object* v___x_842_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v_genTk_839_ = l_Lean_Syntax_getArg(v_x_825_, v___x_838_);
v___x_840_ = lean_unsigned_to_nat(1u);
v_opTk_841_ = l_Lean_Syntax_getArg(v_x_825_, v___x_840_);
lean_dec(v_x_825_);
v___x_842_ = l_Lean_Fmt_fmtGrindFilterGenCmp(v_genTk_839_, v_opTk_841_, v_n_833_, v_a_826_, v_a_827_);
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterGenGeAscii___boxed(lean_object* v_x_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Fmt_fmtGrindFilterGenGeAscii(v_x_843_, v_a_844_, v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1(){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_853_ = l_Lean_Fmt_fmtAttribute;
v___x_854_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenGeAscii___closed__1));
v___x_855_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___closed__1));
v___x_856_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterGenGeAscii___boxed), 3, 0);
v___x_857_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_853_, v___x_854_, v___x_855_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1___boxed(lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1();
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterParen(lean_object* v_x_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterParen___closed__1));
lean_inc(v_x_867_);
v___x_871_ = l_Lean_Syntax_isOfKind(v_x_867_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v_x_867_);
v___x_872_ = l_Lean_Fmt_Error_partialFormatter;
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v_a_869_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v_lbTk_875_; lean_object* v___x_876_; 
v___x_874_ = lean_unsigned_to_nat(0u);
v_lbTk_875_ = l_Lean_Syntax_getArg(v_x_867_, v___x_874_);
v___x_876_ = l_Lean_Fmt_fmt(v_lbTk_875_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
v_a_878_ = lean_ctor_get(v___x_876_, 1);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_876_, 2);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = l_Lean_Syntax_getArg(v_x_867_, v___x_879_);
v___x_881_ = l_Lean_Fmt_fmt(v___x_880_, v_a_868_, v_a_878_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v_rbTk_885_; lean_object* v___x_886_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
v_a_883_ = lean_ctor_get(v___x_881_, 1);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_881_, 2);
v___x_884_ = lean_unsigned_to_nat(2u);
v_rbTk_885_ = l_Lean_Syntax_getArg(v_x_867_, v___x_884_);
lean_dec(v_x_867_);
v___x_886_ = l_Lean_Fmt_fmt(v_rbTk_885_, v_a_868_, v_a_883_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_896_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_a_888_ = lean_ctor_get(v___x_886_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_896_ == 0)
{
v___x_890_ = v___x_886_;
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = l_Lean_Fmt_Layouts_parens(v_a_877_, v_a_882_, v_a_887_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_892_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_a_888_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_dec(v_a_882_);
lean_dec(v_a_877_);
return v___x_886_;
}
}
else
{
lean_dec(v_a_877_);
lean_dec(v_x_867_);
return v___x_881_;
}
}
else
{
lean_dec(v_x_867_);
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterParen___boxed(lean_object* v_x_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Fmt_fmtGrindFilterParen(v_x_897_, v_a_898_, v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1(){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_907_ = l_Lean_Fmt_fmtAttribute;
v___x_908_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterParen___closed__1));
v___x_909_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___closed__1));
v___x_910_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterParen___boxed), 3, 0);
v___x_911_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_907_, v___x_908_, v___x_909_, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1___boxed(lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1();
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterAnd(lean_object* v_x_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterAnd___closed__1));
lean_inc(v_x_921_);
v___x_925_ = l_Lean_Syntax_isOfKind(v_x_921_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_x_921_);
v___x_926_ = l_Lean_Fmt_Error_partialFormatter;
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_923_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l_Lean_Syntax_getArg(v_x_921_, v___x_928_);
v___x_930_ = l_Lean_Fmt_fmt(v___x_929_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v_opTk_934_; lean_object* v___x_935_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
v_a_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_930_, 2);
v___x_933_ = lean_unsigned_to_nat(1u);
v_opTk_934_ = l_Lean_Syntax_getArg(v_x_921_, v___x_933_);
v___x_935_ = l_Lean_Fmt_fmt(v_opTk_934_, v_a_922_, v_a_932_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v_a_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
v_a_937_ = lean_ctor_get(v___x_935_, 1);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_935_, 2);
v___x_938_ = lean_unsigned_to_nat(2u);
v___x_939_ = l_Lean_Syntax_getArg(v_x_921_, v___x_938_);
lean_dec(v_x_921_);
v___x_940_ = l_Lean_Fmt_fmt(v___x_939_, v_a_922_, v_a_937_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_957_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_a_942_ = lean_ctor_get(v___x_940_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_957_ == 0)
{
v___x_944_ = v___x_940_;
v_isShared_945_ = v_isSharedCheck_957_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_957_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_946_ = lean_unsigned_to_nat(3u);
v___x_947_ = lean_mk_empty_array_with_capacity(v___x_946_);
v___x_948_ = lean_array_push(v___x_947_, v_a_931_);
v___x_949_ = lean_array_push(v___x_948_, v_a_936_);
v___x_950_ = lean_array_push(v___x_949_, v_a_941_);
v___x_951_ = 0;
v___x_952_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_952_, 0, v___x_925_);
lean_ctor_set_uint8(v___x_952_, 1, v___x_951_);
lean_ctor_set_uint8(v___x_952_, 2, v___x_925_);
lean_ctor_set_uint8(v___x_952_, 3, v___x_925_);
v___x_953_ = l_Lean_Fmt_Layouts_infixOperator(v___x_950_, v___x_952_);
lean_dec_ref_known(v___x_952_, 0);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_953_);
v___x_955_ = v___x_944_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_a_942_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_dec(v_a_936_);
lean_dec(v_a_931_);
return v___x_940_;
}
}
else
{
lean_dec(v_a_931_);
lean_dec(v_x_921_);
return v___x_935_;
}
}
else
{
lean_dec(v_x_921_);
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterAnd___boxed(lean_object* v_x_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Fmt_fmtGrindFilterAnd(v_x_958_, v_a_959_, v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1(){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_968_ = l_Lean_Fmt_fmtAttribute;
v___x_969_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterAnd___closed__1));
v___x_970_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___closed__1));
v___x_971_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterAnd___boxed), 3, 0);
v___x_972_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_968_, v___x_969_, v___x_970_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1___boxed(lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1();
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterOr(lean_object* v_x_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterOr___closed__1));
lean_inc(v_x_982_);
v___x_986_ = l_Lean_Syntax_isOfKind(v_x_982_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v_x_982_);
v___x_987_ = l_Lean_Fmt_Error_partialFormatter;
v___x_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v_a_984_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = l_Lean_Syntax_getArg(v_x_982_, v___x_989_);
v___x_991_ = l_Lean_Fmt_fmt(v___x_990_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v_opTk_995_; lean_object* v___x_996_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
v_a_993_ = lean_ctor_get(v___x_991_, 1);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_991_, 2);
v___x_994_ = lean_unsigned_to_nat(1u);
v_opTk_995_ = l_Lean_Syntax_getArg(v_x_982_, v___x_994_);
v___x_996_ = l_Lean_Fmt_fmt(v_opTk_995_, v_a_983_, v_a_993_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
v_a_998_ = lean_ctor_get(v___x_996_, 1);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_996_, 2);
v___x_999_ = lean_unsigned_to_nat(2u);
v___x_1000_ = l_Lean_Syntax_getArg(v_x_982_, v___x_999_);
lean_dec(v_x_982_);
v___x_1001_ = l_Lean_Fmt_fmt(v___x_1000_, v_a_983_, v_a_998_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1018_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_a_1003_ = lean_ctor_get(v___x_1001_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1005_ = v___x_1001_;
v_isShared_1006_ = v_isSharedCheck_1018_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1018_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1007_ = lean_unsigned_to_nat(3u);
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_1007_);
v___x_1009_ = lean_array_push(v___x_1008_, v_a_992_);
v___x_1010_ = lean_array_push(v___x_1009_, v_a_997_);
v___x_1011_ = lean_array_push(v___x_1010_, v_a_1002_);
v___x_1012_ = 0;
v___x_1013_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1013_, 0, v___x_986_);
lean_ctor_set_uint8(v___x_1013_, 1, v___x_1012_);
lean_ctor_set_uint8(v___x_1013_, 2, v___x_986_);
lean_ctor_set_uint8(v___x_1013_, 3, v___x_986_);
v___x_1014_ = l_Lean_Fmt_Layouts_infixOperator(v___x_1011_, v___x_1013_);
lean_dec_ref_known(v___x_1013_, 0);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1014_);
v___x_1016_ = v___x_1005_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_a_1003_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
else
{
lean_dec(v_a_997_);
lean_dec(v_a_992_);
return v___x_1001_;
}
}
else
{
lean_dec(v_a_992_);
lean_dec(v_x_982_);
return v___x_996_;
}
}
else
{
lean_dec(v_x_982_);
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterOr___boxed(lean_object* v_x_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Fmt_fmtGrindFilterOr(v_x_1019_, v_a_1020_, v_a_1021_);
lean_dec_ref(v_a_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1(){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1029_ = l_Lean_Fmt_fmtAttribute;
v___x_1030_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterOr___closed__1));
v___x_1031_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___closed__1));
v___x_1032_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterOr___boxed), 3, 0);
v___x_1033_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1029_, v___x_1030_, v___x_1031_, v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1___boxed(lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1();
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterNot(lean_object* v_x_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterNot___closed__1));
lean_inc(v_x_1043_);
v___x_1047_ = l_Lean_Syntax_isOfKind(v_x_1043_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v_x_1043_);
v___x_1048_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v_a_1045_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v_bangTk_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_unsigned_to_nat(0u);
v_bangTk_1051_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1050_);
v___x_1052_ = l_Lean_Fmt_fmt(v_bangTk_1051_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
v_a_1054_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1052_, 2);
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = l_Lean_Syntax_getArg(v_x_1043_, v___x_1055_);
lean_dec(v_x_1043_);
v___x_1057_ = l_Lean_Fmt_fmt(v___x_1056_, v_a_1044_, v_a_1054_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1068_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_a_1059_ = lean_ctor_get(v___x_1057_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1061_ = v___x_1057_;
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1063_ = 1;
v___x_1064_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_1053_, v_a_1058_, v___x_1063_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1064_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_a_1059_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
lean_dec(v_a_1053_);
return v___x_1057_;
}
}
else
{
lean_dec(v_x_1043_);
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilterNot___boxed(lean_object* v_x_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Fmt_fmtGrindFilterNot(v_x_1069_, v_a_1070_, v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1(){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1079_ = l_Lean_Fmt_fmtAttribute;
v___x_1080_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterNot___closed__1));
v___x_1081_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___closed__1));
v___x_1082_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilterNot___boxed), 3, 0);
v___x_1083_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1079_, v___x_1080_, v___x_1081_, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1___boxed(lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1();
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilter(lean_object* v_x_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
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
lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = l_Lean_Syntax_getArg(v_x_1093_, v___x_1100_);
lean_dec(v_x_1093_);
v___x_1102_ = l_Lean_Syntax_isNone(v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1101_);
v___x_1104_ = l_Lean_Syntax_matchesNull(v___x_1101_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v___x_1101_);
v___x_1105_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v_a_1095_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = l_Lean_Syntax_getArg(v___x_1101_, v___x_1100_);
lean_dec(v___x_1101_);
v___x_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
v___x_1109_ = l_Lean_Fmt_fmt_x3f(v___x_1108_, v_a_1094_, v_a_1095_);
return v___x_1109_;
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v___x_1101_);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_Fmt_fmt_x3f(v___x_1110_, v_a_1094_, v_a_1095_);
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFilter___boxed(lean_object* v_x_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Fmt_fmtGrindFilter(v_x_1112_, v_a_1113_, v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1(){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1122_ = l_Lean_Fmt_fmtAttribute;
v___x_1123_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
v___x_1124_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___closed__1));
v___x_1125_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFilter___boxed), 3, 0);
v___x_1126_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1122_, v___x_1123_, v___x_1124_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1___boxed(lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1();
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefAnchor(lean_object* v_x_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRefAnchor___closed__1));
lean_inc(v_x_1136_);
v___x_1140_ = l_Lean_Syntax_isOfKind(v_x_1136_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec(v_x_1136_);
v___x_1141_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v_a_1138_);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = l_Lean_Syntax_getArg(v_x_1136_, v___x_1143_);
lean_dec(v_x_1136_);
v___x_1145_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnchor___closed__4));
lean_inc(v___x_1144_);
v___x_1146_ = l_Lean_Syntax_isOfKind(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec(v___x_1144_);
v___x_1147_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v_a_1138_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Fmt_fmt(v___x_1144_, v_a_1137_, v_a_1138_);
return v___x_1149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefAnchor___boxed(lean_object* v_x_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Fmt_fmtGrindRefAnchor(v_x_1150_, v_a_1151_, v_a_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1(){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1160_ = l_Lean_Fmt_fmtAttribute;
v___x_1161_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRefAnchor___closed__1));
v___x_1162_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___closed__1));
v___x_1163_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindRefAnchor___boxed), 3, 0);
v___x_1164_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1160_, v___x_1161_, v___x_1162_, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1___boxed(lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1();
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefAnchordOrd(lean_object* v_x_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1));
lean_inc(v_x_1174_);
v___x_1178_ = l_Lean_Syntax_isOfKind(v_x_1174_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_x_1174_);
v___x_1179_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v_a_1176_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = l_Lean_Syntax_getArg(v_x_1174_, v___x_1181_);
v___x_1183_ = l_Lean_Fmt_fmt(v___x_1182_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v_slashTk_1187_; lean_object* v___x_1188_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
v_a_1185_ = lean_ctor_get(v___x_1183_, 1);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1183_, 2);
v___x_1186_ = lean_unsigned_to_nat(1u);
v_slashTk_1187_ = l_Lean_Syntax_getArg(v_x_1174_, v___x_1186_);
v___x_1188_ = l_Lean_Fmt_fmt(v_slashTk_1187_, v_a_1175_, v_a_1185_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
v_a_1190_ = lean_ctor_get(v___x_1188_, 1);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1188_, 2);
v___x_1191_ = lean_unsigned_to_nat(2u);
v___x_1192_ = l_Lean_Syntax_getArg(v_x_1174_, v___x_1191_);
lean_dec(v_x_1174_);
v___x_1193_ = l_Lean_Fmt_fmt(v___x_1192_, v_a_1175_, v_a_1190_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1208_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_a_1195_ = lean_ctor_get(v___x_1193_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1197_ = v___x_1193_;
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1199_ = lean_unsigned_to_nat(3u);
v___x_1200_ = lean_mk_empty_array_with_capacity(v___x_1199_);
v___x_1201_ = lean_array_push(v___x_1200_, v_a_1184_);
v___x_1202_ = lean_array_push(v___x_1201_, v_a_1189_);
v___x_1203_ = lean_array_push(v___x_1202_, v_a_1194_);
v___x_1204_ = l_Lean_Fmt_Layouts_atomicInfixOperator(v___x_1203_);
lean_dec_ref(v___x_1203_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1204_);
v___x_1206_ = v___x_1197_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_a_1195_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_dec(v_a_1189_);
lean_dec(v_a_1184_);
return v___x_1193_;
}
}
else
{
lean_dec(v_a_1184_);
lean_dec(v_x_1174_);
return v___x_1188_;
}
}
else
{
lean_dec(v_x_1174_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefAnchordOrd___boxed(lean_object* v_x_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Fmt_fmtGrindRefAnchordOrd(v_x_1209_, v_a_1210_, v_a_1211_);
lean_dec_ref(v_a_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1(){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1219_ = l_Lean_Fmt_fmtAttribute;
v___x_1220_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRefAnchordOrd___closed__1));
v___x_1221_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___closed__1));
v___x_1222_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindRefAnchordOrd___boxed), 3, 0);
v___x_1223_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1219_, v___x_1220_, v___x_1221_, v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1___boxed(lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1();
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefTerm(lean_object* v_x_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRefTerm___closed__1));
lean_inc(v_x_1233_);
v___x_1237_ = l_Lean_Syntax_isOfKind(v_x_1233_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v_x_1233_);
v___x_1238_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v_a_1235_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = l_Lean_Syntax_getArg(v_x_1233_, v___x_1240_);
lean_dec(v_x_1233_);
v___x_1242_ = l_Lean_Fmt_fmt(v___x_1241_, v_a_1234_, v_a_1235_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRefTerm___boxed(lean_object* v_x_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Fmt_fmtGrindRefTerm(v_x_1243_, v_a_1244_, v_a_1245_);
lean_dec_ref(v_a_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1(){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1253_ = l_Lean_Fmt_fmtAttribute;
v___x_1254_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRefTerm___closed__1));
v___x_1255_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___closed__1));
v___x_1256_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindRefTerm___boxed), 3, 0);
v___x_1257_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1253_, v___x_1254_, v___x_1255_, v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1___boxed(lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1();
return v_res_1259_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtGrindStep___closed__1(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = ((lean_object*)(l_Lean_Fmt_fmtGrindStep___closed__0));
v___x_1262_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindStep(lean_object* v_x_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_Fmt_fmtGrindStep___closed__3));
lean_inc(v_x_1271_);
v___x_1313_ = l_Lean_Syntax_isOfKind(v_x_1271_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v_x_1271_);
v___x_1314_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v_a_1273_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_pipeTk_x3f_1319_; lean_object* v_f_x3f_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = l_Lean_Syntax_getArg(v_x_1271_, v___x_1316_);
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = l_Lean_Syntax_getArg(v_x_1271_, v___x_1342_);
lean_dec(v_x_1271_);
v___x_1344_ = l_Lean_Syntax_isNone(v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1343_);
v___x_1346_ = l_Lean_Syntax_matchesNull(v___x_1343_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec(v___x_1343_);
lean_dec(v___x_1317_);
v___x_1347_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_a_1273_);
return v___x_1348_;
}
else
{
lean_object* v_pipeTk_x3f_1349_; lean_object* v_f_x3f_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_pipeTk_x3f_1349_ = l_Lean_Syntax_getArg(v___x_1343_, v___x_1316_);
v___x_1356_ = l_Lean_Syntax_getArg(v___x_1343_, v___x_1342_);
lean_dec(v___x_1343_);
v___x_1357_ = l_Lean_Syntax_isNone(v___x_1356_);
if (v___x_1357_ == 0)
{
uint8_t v___x_1358_; 
lean_inc(v___x_1356_);
v___x_1358_ = l_Lean_Syntax_matchesNull(v___x_1356_, v___x_1342_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v___x_1356_);
lean_dec(v_pipeTk_x3f_1349_);
lean_dec(v___x_1317_);
v___x_1359_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v_a_1273_);
return v___x_1360_;
}
else
{
lean_object* v_f_x3f_1361_; lean_object* v___x_1362_; 
v_f_x3f_1361_ = l_Lean_Syntax_getArg(v___x_1356_, v___x_1316_);
lean_dec(v___x_1356_);
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_f_x3f_1361_);
v_f_x3f_1351_ = v___x_1362_;
v___y_1352_ = v_a_1272_;
v___y_1353_ = v_a_1273_;
goto v___jp_1350_;
}
}
else
{
lean_object* v___x_1363_; 
lean_dec(v___x_1356_);
v___x_1363_ = lean_box(0);
v_f_x3f_1351_ = v___x_1363_;
v___y_1352_ = v_a_1272_;
v___y_1353_ = v_a_1273_;
goto v___jp_1350_;
}
v___jp_1350_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_pipeTk_x3f_1349_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_f_x3f_1351_);
v_pipeTk_x3f_1319_ = v___x_1354_;
v_f_x3f_1320_ = v___x_1355_;
v___y_1321_ = v___y_1352_;
v___y_1322_ = v___y_1353_;
goto v___jp_1318_;
}
}
}
else
{
lean_object* v___x_1364_; 
lean_dec(v___x_1343_);
v___x_1364_ = lean_box(0);
v_pipeTk_x3f_1319_ = v___x_1364_;
v_f_x3f_1320_ = v___x_1364_;
v___y_1321_ = v_a_1272_;
v___y_1322_ = v_a_1273_;
goto v___jp_1318_;
}
v___jp_1318_:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Fmt_fmt(v___x_1317_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v_a_1325_; lean_object* v___x_1326_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
v_a_1325_ = lean_ctor_get(v___x_1323_, 1);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1323_, 2);
v___x_1326_ = l_Lean_Fmt_fmt_x3f(v_pipeTk_x3f_1319_, v___y_1321_, v_a_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
if (lean_obj_tag(v_f_x3f_1320_) == 0)
{
lean_object* v_a_1327_; lean_object* v_a_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
v_a_1328_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1326_, 2);
v___y_1307_ = v_a_1324_;
v___y_1308_ = v_a_1327_;
v___y_1309_ = v_a_1328_;
v___y_1310_ = v___y_1321_;
goto v___jp_1306_;
}
else
{
lean_object* v_val_1329_; 
v_val_1329_ = lean_ctor_get(v_f_x3f_1320_, 0);
lean_inc(v_val_1329_);
lean_dec_ref_known(v_f_x3f_1320_, 1);
if (lean_obj_tag(v_val_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v_a_1331_; 
v_a_1330_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1330_);
v_a_1331_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1326_, 2);
v___y_1307_ = v_a_1324_;
v___y_1308_ = v_a_1330_;
v___y_1309_ = v_a_1331_;
v___y_1310_ = v___y_1321_;
goto v___jp_1306_;
}
else
{
lean_object* v_a_1332_; lean_object* v_a_1333_; lean_object* v_val_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_a_1332_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1332_);
v_a_1333_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1326_, 2);
v_val_1334_ = lean_ctor_get(v_val_1329_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_val_1329_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v_val_1329_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_val_1334_);
lean_dec(v_val_1329_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_val_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
v___y_1275_ = v_a_1324_;
v___y_1276_ = v_a_1332_;
v___y_1277_ = v_a_1333_;
v___y_1278_ = v___y_1321_;
v___y_1279_ = v___x_1339_;
goto v___jp_1274_;
}
}
}
}
}
else
{
lean_dec(v_a_1324_);
lean_dec(v_f_x3f_1320_);
return v___x_1326_;
}
}
else
{
lean_dec(v_f_x3f_1320_);
lean_dec(v_pipeTk_x3f_1319_);
return v___x_1323_;
}
}
}
v___jp_1274_:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Fmt_fmt_x3f(v___y_1279_, v___y_1278_, v___y_1277_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1305_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_a_1282_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1284_ = v___x_1280_;
v_isShared_1285_ = v_isSharedCheck_1305_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1305_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1286_ = lean_unsigned_to_nat(2u);
v___x_1287_ = lean_mk_empty_array_with_capacity(v___x_1286_);
lean_inc_ref(v___x_1287_);
v___x_1288_ = lean_array_push(v___x_1287_, v___y_1276_);
v___x_1289_ = lean_array_push(v___x_1288_, v_a_1281_);
v___x_1290_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_1289_);
lean_dec_ref(v___x_1289_);
v___x_1291_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1290_);
v___x_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___y_1275_);
v___x_1293_ = lean_obj_once(&l_Lean_Fmt_fmtGrindStep___closed__1, &l_Lean_Fmt_fmtGrindStep___closed__1_once, _init_l_Lean_Fmt_fmtGrindStep___closed__1);
v___x_1294_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1292_, v___x_1293_);
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1291_);
v___x_1297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
lean_ctor_set(v___x_1297_, 2, v___x_1295_);
v___x_1298_ = lean_array_push(v___x_1287_, v___x_1294_);
v___x_1299_ = lean_array_push(v___x_1298_, v___x_1297_);
v___x_1300_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1299_);
lean_dec_ref(v___x_1299_);
v___x_1301_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_1300_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1301_);
v___x_1303_ = v___x_1284_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_a_1282_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_dec_ref(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v___x_1280_;
}
}
v___jp_1306_:
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_box(0);
v___y_1275_ = v___y_1307_;
v___y_1276_ = v___y_1308_;
v___y_1277_ = v___y_1309_;
v___y_1278_ = v___y_1310_;
v___y_1279_ = v___x_1311_;
goto v___jp_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindStep___boxed(lean_object* v_x_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Fmt_fmtGrindStep(v_x_1365_, v_a_1366_, v_a_1367_);
lean_dec_ref(v_a_1366_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1(){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1375_ = l_Lean_Fmt_fmtAttribute;
v___x_1376_ = ((lean_object*)(l_Lean_Fmt_fmtGrindStep___closed__3));
v___x_1377_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___closed__1));
v___x_1378_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindStep___boxed), 3, 0);
v___x_1379_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1375_, v___x_1376_, v___x_1377_, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1___boxed(lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1();
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeq1Indented(lean_object* v_x_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq1Indented___closed__1));
lean_inc(v_x_1390_);
v___x_1394_ = l_Lean_Syntax_isOfKind(v_x_1390_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v_x_1390_);
v___x_1395_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v_a_1392_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_steps_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = l_Lean_Syntax_getArg(v_x_1390_, v___x_1397_);
lean_dec(v_x_1390_);
v___x_1399_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq1Indented___closed__2));
v_steps_1400_ = l_Lean_Syntax_getArgs(v___x_1398_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v___x_1402_ = l_Lean_Fmt_fmtSeq___redArg(v___x_1399_, v_steps_1400_, v___x_1401_, v_a_1391_, v_a_1392_);
lean_dec_ref(v_steps_1400_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeq1Indented___boxed(lean_object* v_x_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Fmt_fmtGrindSeq1Indented(v_x_1403_, v_a_1404_, v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1(){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1413_ = l_Lean_Fmt_fmtAttribute;
v___x_1414_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq1Indented___closed__1));
v___x_1415_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___closed__1));
v___x_1416_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSeq1Indented___boxed), 3, 0);
v___x_1417_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1413_, v___x_1414_, v___x_1415_, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1___boxed(lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1();
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeqBracketed(lean_object* v_x_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeqBracketed___closed__1));
lean_inc(v_x_1427_);
v___x_1431_ = l_Lean_Syntax_isOfKind(v_x_1427_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_x_1427_);
v___x_1432_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v_a_1429_);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; lean_object* v_lbTk_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v_lbTk_1435_ = l_Lean_Syntax_getArg(v_x_1427_, v___x_1434_);
v___x_1436_ = l_Lean_Fmt_fmt(v_lbTk_1435_, v_a_1428_, v_a_1429_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v_steps_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
v_a_1438_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1436_, 2);
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = l_Lean_Syntax_getArg(v_x_1427_, v___x_1439_);
v___x_1441_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq1Indented___closed__2));
v_steps_1442_ = l_Lean_Syntax_getArgs(v___x_1440_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v___x_1444_ = l_Lean_Fmt_fmtSeq___redArg(v___x_1441_, v_steps_1442_, v___x_1443_, v_a_1428_, v_a_1438_);
lean_dec_ref(v_steps_1442_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v_a_1446_; lean_object* v___x_1447_; lean_object* v_rbTk_1448_; lean_object* v___x_1449_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
v_a_1446_ = lean_ctor_get(v___x_1444_, 1);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1444_, 2);
v___x_1447_ = lean_unsigned_to_nat(2u);
v_rbTk_1448_ = l_Lean_Syntax_getArg(v_x_1427_, v___x_1447_);
lean_dec(v_x_1427_);
v___x_1449_ = l_Lean_Fmt_fmt(v_rbTk_1448_, v_a_1428_, v_a_1446_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1462_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_a_1451_ = lean_ctor_get(v___x_1449_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1453_ = v___x_1449_;
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1455_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_1456_ = 1;
v___x_1457_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*1, v___x_1431_);
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*1 + 1, v___x_1456_);
v___x_1458_ = l_Lean_Fmt_Layouts_bracketed(v_a_1437_, v_a_1445_, v_a_1450_, v___x_1457_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1458_);
v___x_1460_ = v___x_1453_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1451_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_dec(v_a_1445_);
lean_dec(v_a_1437_);
return v___x_1449_;
}
}
else
{
lean_dec(v_a_1437_);
lean_dec(v_x_1427_);
return v___x_1444_;
}
}
else
{
lean_dec(v_x_1427_);
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeqBracketed___boxed(lean_object* v_x_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Fmt_fmtGrindSeqBracketed(v_x_1463_, v_a_1464_, v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1(){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1473_ = l_Lean_Fmt_fmtAttribute;
v___x_1474_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeqBracketed___closed__1));
v___x_1475_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___closed__1));
v___x_1476_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSeqBracketed___boxed), 3, 0);
v___x_1477_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1473_, v___x_1474_, v___x_1475_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1___boxed(lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1();
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeq(lean_object* v_x_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v_x_1487_);
v___x_1491_ = l_Lean_Syntax_isOfKind(v_x_1487_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v_x_1487_);
v___x_1492_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v_a_1489_);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = l_Lean_Syntax_getArg(v_x_1487_, v___x_1494_);
lean_dec(v_x_1487_);
v___x_1496_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq1Indented___closed__1));
lean_inc(v___x_1495_);
v___x_1497_ = l_Lean_Syntax_isOfKind(v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeqBracketed___closed__1));
lean_inc(v___x_1495_);
v___x_1499_ = l_Lean_Syntax_isOfKind(v___x_1495_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec(v___x_1495_);
v___x_1500_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v_a_1489_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Fmt_fmt(v___x_1495_, v_a_1488_, v_a_1489_);
return v___x_1502_;
}
}
else
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Fmt_fmt(v___x_1495_, v_a_1488_, v_a_1489_);
return v___x_1503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSeq___boxed(lean_object* v_x_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Fmt_fmtGrindSeq(v_x_1504_, v_a_1505_, v_a_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1(){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1514_ = l_Lean_Fmt_fmtAttribute;
v___x_1515_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
v___x_1516_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___closed__1));
v___x_1517_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSeq___boxed), 3, 0);
v___x_1518_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1514_, v___x_1515_, v___x_1516_, v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1___boxed(lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1();
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindKeywordFilter(lean_object* v_tk_1524_, lean_object* v_f_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Fmt_fmt(v_tk_1524_, v_a_1526_, v_a_1527_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
v_a_1530_ = lean_ctor_get(v___x_1528_, 1);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1528_, 2);
v___x_1531_ = l_Lean_Fmt_fmt(v_f_1525_, v_a_1526_, v_a_1530_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1546_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_a_1533_ = lean_ctor_get(v___x_1531_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1535_ = v___x_1531_;
v_isShared_1536_ = v_isSharedCheck_1546_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1546_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1537_ = lean_unsigned_to_nat(2u);
v___x_1538_ = lean_mk_empty_array_with_capacity(v___x_1537_);
v___x_1539_ = lean_array_push(v___x_1538_, v_a_1529_);
v___x_1540_ = lean_array_push(v___x_1539_, v_a_1532_);
v___x_1541_ = ((lean_object*)(l_Lean_Fmt_fmtGrindKeywordFilter___closed__0));
v___x_1542_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1540_, v___x_1541_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1542_);
v___x_1544_ = v___x_1535_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_a_1533_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_dec(v_a_1529_);
return v___x_1531_;
}
}
else
{
lean_dec(v_f_1525_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindKeywordFilter___boxed(lean_object* v_tk_1547_, lean_object* v_f_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Fmt_fmtGrindKeywordFilter(v_tk_1547_, v_f_1548_, v_a_1549_, v_a_1550_);
lean_dec_ref(v_a_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowAsserted(lean_object* v_x_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowAsserted___closed__1));
lean_inc(v_x_1559_);
v___x_1563_ = l_Lean_Syntax_isOfKind(v_x_1559_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec(v_x_1559_);
v___x_1564_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v_a_1561_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; lean_object* v_f_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1566_ = lean_unsigned_to_nat(1u);
v_f_1567_ = l_Lean_Syntax_getArg(v_x_1559_, v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
lean_inc(v_f_1567_);
v___x_1569_ = l_Lean_Syntax_isOfKind(v_f_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v_f_1567_);
lean_dec(v_x_1559_);
v___x_1570_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v_a_1561_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; lean_object* v_tk_1573_; lean_object* v___x_1574_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v_tk_1573_ = l_Lean_Syntax_getArg(v_x_1559_, v___x_1572_);
lean_dec(v_x_1559_);
v___x_1574_ = l_Lean_Fmt_fmtGrindKeywordFilter(v_tk_1573_, v_f_1567_, v_a_1560_, v_a_1561_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowAsserted___boxed(lean_object* v_x_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Fmt_fmtGrindShowAsserted(v_x_1575_, v_a_1576_, v_a_1577_);
lean_dec_ref(v_a_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1(){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1585_ = l_Lean_Fmt_fmtAttribute;
v___x_1586_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowAsserted___closed__1));
v___x_1587_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___closed__1));
v___x_1588_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindShowAsserted___boxed), 3, 0);
v___x_1589_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1585_, v___x_1586_, v___x_1587_, v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1___boxed(lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1();
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowTrue(lean_object* v_x_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowTrue___closed__1));
lean_inc(v_x_1599_);
v___x_1603_ = l_Lean_Syntax_isOfKind(v_x_1599_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_x_1599_);
v___x_1604_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v_a_1601_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v_f_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
v_f_1607_ = l_Lean_Syntax_getArg(v_x_1599_, v___x_1606_);
v___x_1608_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
lean_inc(v_f_1607_);
v___x_1609_ = l_Lean_Syntax_isOfKind(v_f_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v_f_1607_);
lean_dec(v_x_1599_);
v___x_1610_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_a_1601_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v_tk_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
v_tk_1613_ = l_Lean_Syntax_getArg(v_x_1599_, v___x_1612_);
lean_dec(v_x_1599_);
v___x_1614_ = l_Lean_Fmt_fmtGrindKeywordFilter(v_tk_1613_, v_f_1607_, v_a_1600_, v_a_1601_);
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowTrue___boxed(lean_object* v_x_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Fmt_fmtGrindShowTrue(v_x_1615_, v_a_1616_, v_a_1617_);
lean_dec_ref(v_a_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1(){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1625_ = l_Lean_Fmt_fmtAttribute;
v___x_1626_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowTrue___closed__1));
v___x_1627_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___closed__1));
v___x_1628_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindShowTrue___boxed), 3, 0);
v___x_1629_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1625_, v___x_1626_, v___x_1627_, v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1___boxed(lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1();
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowFalse(lean_object* v_x_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowFalse___closed__1));
lean_inc(v_x_1639_);
v___x_1643_ = l_Lean_Syntax_isOfKind(v_x_1639_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v_x_1639_);
v___x_1644_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v_a_1641_);
return v___x_1645_;
}
else
{
lean_object* v___x_1646_; lean_object* v_f_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1646_ = lean_unsigned_to_nat(1u);
v_f_1647_ = l_Lean_Syntax_getArg(v_x_1639_, v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
lean_inc(v_f_1647_);
v___x_1649_ = l_Lean_Syntax_isOfKind(v_f_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v_f_1647_);
lean_dec(v_x_1639_);
v___x_1650_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_a_1641_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; lean_object* v_tk_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_unsigned_to_nat(0u);
v_tk_1653_ = l_Lean_Syntax_getArg(v_x_1639_, v___x_1652_);
lean_dec(v_x_1639_);
v___x_1654_ = l_Lean_Fmt_fmtGrindKeywordFilter(v_tk_1653_, v_f_1647_, v_a_1640_, v_a_1641_);
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowFalse___boxed(lean_object* v_x_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Fmt_fmtGrindShowFalse(v_x_1655_, v_a_1656_, v_a_1657_);
lean_dec_ref(v_a_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1(){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1665_ = l_Lean_Fmt_fmtAttribute;
v___x_1666_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowFalse___closed__1));
v___x_1667_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___closed__1));
v___x_1668_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindShowFalse___boxed), 3, 0);
v___x_1669_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1665_, v___x_1666_, v___x_1667_, v___x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1___boxed(lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1();
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowEqcs(lean_object* v_x_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowEqcs___closed__1));
lean_inc(v_x_1679_);
v___x_1683_ = l_Lean_Syntax_isOfKind(v_x_1679_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec(v_x_1679_);
v___x_1684_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v_a_1681_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v_f_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1686_ = lean_unsigned_to_nat(1u);
v_f_1687_ = l_Lean_Syntax_getArg(v_x_1679_, v___x_1686_);
v___x_1688_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
lean_inc(v_f_1687_);
v___x_1689_ = l_Lean_Syntax_isOfKind(v_f_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_f_1687_);
lean_dec(v_x_1679_);
v___x_1690_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v_a_1681_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v_tk_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_unsigned_to_nat(0u);
v_tk_1693_ = l_Lean_Syntax_getArg(v_x_1679_, v___x_1692_);
lean_dec(v_x_1679_);
v___x_1694_ = l_Lean_Fmt_fmtGrindKeywordFilter(v_tk_1693_, v_f_1687_, v_a_1680_, v_a_1681_);
return v___x_1694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowEqcs___boxed(lean_object* v_x_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Fmt_fmtGrindShowEqcs(v_x_1695_, v_a_1696_, v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1(){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1705_ = l_Lean_Fmt_fmtAttribute;
v___x_1706_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowEqcs___closed__1));
v___x_1707_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___closed__1));
v___x_1708_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindShowEqcs___boxed), 3, 0);
v___x_1709_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1705_, v___x_1706_, v___x_1707_, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1___boxed(lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1();
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowCases(lean_object* v_x_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowCases___closed__1));
lean_inc(v_x_1719_);
v___x_1723_ = l_Lean_Syntax_isOfKind(v_x_1719_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec(v_x_1719_);
v___x_1724_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set(v___x_1725_, 1, v_a_1721_);
return v___x_1725_;
}
else
{
lean_object* v___x_1726_; lean_object* v_f_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1726_ = lean_unsigned_to_nat(1u);
v_f_1727_ = l_Lean_Syntax_getArg(v_x_1719_, v___x_1726_);
v___x_1728_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
lean_inc(v_f_1727_);
v___x_1729_ = l_Lean_Syntax_isOfKind(v_f_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_f_1727_);
lean_dec(v_x_1719_);
v___x_1730_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v_a_1721_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; lean_object* v_tk_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_unsigned_to_nat(0u);
v_tk_1733_ = l_Lean_Syntax_getArg(v_x_1719_, v___x_1732_);
lean_dec(v_x_1719_);
v___x_1734_ = l_Lean_Fmt_fmtGrindKeywordFilter(v_tk_1733_, v_f_1727_, v_a_1720_, v_a_1721_);
return v___x_1734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowCases___boxed(lean_object* v_x_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Fmt_fmtGrindShowCases(v_x_1735_, v_a_1736_, v_a_1737_);
lean_dec_ref(v_a_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1(){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1745_ = l_Lean_Fmt_fmtAttribute;
v___x_1746_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowCases___closed__1));
v___x_1747_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___closed__1));
v___x_1748_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindShowCases___boxed), 3, 0);
v___x_1749_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1745_, v___x_1746_, v___x_1747_, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1___boxed(lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1();
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowState(lean_object* v_x_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowState___closed__1));
lean_inc(v_x_1759_);
v___x_1763_ = l_Lean_Syntax_isOfKind(v_x_1759_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v_x_1759_);
v___x_1764_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v_a_1761_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; lean_object* v_f_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1766_ = lean_unsigned_to_nat(1u);
v_f_1767_ = l_Lean_Syntax_getArg(v_x_1759_, v___x_1766_);
v___x_1768_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
lean_inc(v_f_1767_);
v___x_1769_ = l_Lean_Syntax_isOfKind(v_f_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v_f_1767_);
lean_dec(v_x_1759_);
v___x_1770_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v_a_1761_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v_tk_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_unsigned_to_nat(0u);
v_tk_1773_ = l_Lean_Syntax_getArg(v_x_1759_, v___x_1772_);
lean_dec(v_x_1759_);
v___x_1774_ = l_Lean_Fmt_fmtGrindKeywordFilter(v_tk_1773_, v_f_1767_, v_a_1760_, v_a_1761_);
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowState___boxed(lean_object* v_x_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Fmt_fmtGrindShowState(v_x_1775_, v_a_1776_, v_a_1777_);
lean_dec_ref(v_a_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1(){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1785_ = l_Lean_Fmt_fmtAttribute;
v___x_1786_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowState___closed__1));
v___x_1787_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___closed__1));
v___x_1788_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindShowState___boxed), 3, 0);
v___x_1789_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1785_, v___x_1786_, v___x_1787_, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1___boxed(lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1();
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCasesTrace(lean_object* v_x_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_Fmt_fmtGrindCasesTrace___closed__1));
lean_inc(v_x_1799_);
v___x_1803_ = l_Lean_Syntax_isOfKind(v_x_1799_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v_x_1799_);
v___x_1804_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_a_1801_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v_f_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1806_ = lean_unsigned_to_nat(1u);
v_f_1807_ = l_Lean_Syntax_getArg(v_x_1799_, v___x_1806_);
v___x_1808_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilter___closed__1));
lean_inc(v_f_1807_);
v___x_1809_ = l_Lean_Syntax_isOfKind(v_f_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v_f_1807_);
lean_dec(v_x_1799_);
v___x_1810_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v_a_1801_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v_tk_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v_tk_1813_ = l_Lean_Syntax_getArg(v_x_1799_, v___x_1812_);
lean_dec(v_x_1799_);
v___x_1814_ = l_Lean_Fmt_fmtGrindKeywordFilter(v_tk_1813_, v_f_1807_, v_a_1800_, v_a_1801_);
return v___x_1814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCasesTrace___boxed(lean_object* v_x_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Fmt_fmtGrindCasesTrace(v_x_1815_, v_a_1816_, v_a_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1(){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1825_ = l_Lean_Fmt_fmtAttribute;
v___x_1826_ = ((lean_object*)(l_Lean_Fmt_fmtGrindCasesTrace___closed__1));
v___x_1827_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___closed__1));
v___x_1828_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindCasesTrace___boxed), 3, 0);
v___x_1829_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1825_, v___x_1826_, v___x_1827_, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1___boxed(lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1();
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowTerm(lean_object* v_x_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowTerm___closed__1));
lean_inc(v_x_1839_);
v___x_1843_ = l_Lean_Syntax_isOfKind(v_x_1839_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v_x_1839_);
v___x_1844_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v_a_1841_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = l_Lean_Syntax_getArg(v_x_1839_, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_1847_);
v___x_1849_ = l_Lean_Syntax_isOfKind(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v___x_1847_);
lean_dec(v_x_1839_);
v___x_1850_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v_a_1841_);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; lean_object* v_tk_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_unsigned_to_nat(0u);
v_tk_1853_ = l_Lean_Syntax_getArg(v_x_1839_, v___x_1852_);
lean_dec(v_x_1839_);
v___x_1854_ = l_Lean_Fmt_fmt(v_tk_1853_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v_a_1856_; lean_object* v___x_1857_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
v_a_1856_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1854_, 2);
v___x_1857_ = l_Lean_Fmt_fmt(v___x_1847_, v_a_1840_, v_a_1856_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1868_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_a_1859_ = lean_ctor_get(v___x_1857_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1861_ = v___x_1857_;
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1863_ = 1;
v___x_1864_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1855_, v_a_1858_, v___x_1863_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1864_);
v___x_1866_ = v___x_1861_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_a_1859_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_dec(v_a_1855_);
return v___x_1857_;
}
}
else
{
lean_dec(v___x_1847_);
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindShowTerm___boxed(lean_object* v_x_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Fmt_fmtGrindShowTerm(v_x_1869_, v_a_1870_, v_a_1871_);
lean_dec_ref(v_a_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1(){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1879_ = l_Lean_Fmt_fmtAttribute;
v___x_1880_ = ((lean_object*)(l_Lean_Fmt_fmtGrindShowTerm___closed__1));
v___x_1881_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___closed__1));
v___x_1882_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindShowTerm___boxed), 3, 0);
v___x_1883_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1879_, v___x_1880_, v___x_1881_, v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1___boxed(lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1();
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTacticCases(lean_object* v_x_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTacticCases___closed__1));
lean_inc(v_x_1893_);
v___x_1897_ = l_Lean_Syntax_isOfKind(v_x_1893_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec(v_x_1893_);
v___x_1898_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v_a_1895_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; lean_object* v_tk_1901_; lean_object* v___x_1902_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v_tk_1901_ = l_Lean_Syntax_getArg(v_x_1893_, v___x_1900_);
v___x_1902_ = l_Lean_Fmt_fmt(v_tk_1901_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v_a_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
v_a_1904_ = lean_ctor_get(v___x_1902_, 1);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1902_, 2);
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = l_Lean_Syntax_getArg(v_x_1893_, v___x_1905_);
lean_dec(v_x_1893_);
v___x_1907_ = l_Lean_Fmt_fmt(v___x_1906_, v_a_1894_, v_a_1904_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1923_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_a_1909_ = lean_ctor_get(v___x_1907_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1911_ = v___x_1907_;
v_isShared_1912_ = v_isSharedCheck_1923_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1923_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1913_ = lean_unsigned_to_nat(2u);
v___x_1914_ = lean_mk_empty_array_with_capacity(v___x_1913_);
v___x_1915_ = lean_array_push(v___x_1914_, v_a_1903_);
v___x_1916_ = lean_array_push(v___x_1915_, v_a_1908_);
v___x_1917_ = 0;
v___x_1918_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1918_, 0, v___x_1897_);
lean_ctor_set_uint8(v___x_1918_, 1, v___x_1917_);
lean_ctor_set_uint8(v___x_1918_, 2, v___x_1917_);
lean_ctor_set_uint8(v___x_1918_, 3, v___x_1917_);
v___x_1919_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1916_, v___x_1918_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1919_);
v___x_1921_ = v___x_1911_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_a_1909_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
else
{
lean_dec(v_a_1903_);
return v___x_1907_;
}
}
else
{
lean_dec(v_x_1893_);
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTacticCases___boxed(lean_object* v_x_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_Fmt_fmtGrindTacticCases(v_x_1924_, v_a_1925_, v_a_1926_);
lean_dec_ref(v_a_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1(){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1934_ = l_Lean_Fmt_fmtAttribute;
v___x_1935_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTacticCases___closed__1));
v___x_1936_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___closed__1));
v___x_1937_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindTacticCases___boxed), 3, 0);
v___x_1938_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1934_, v___x_1935_, v___x_1936_, v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1___boxed(lean_object* v_a_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1();
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindWithAnnotateState(lean_object* v_stx_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_1941_, v___x_1944_, v_a_1943_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v_a_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
v_a_1947_ = lean_ctor_get(v___x_1945_, 1);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1945_, 2);
v___x_1948_ = lean_unsigned_to_nat(1u);
v___x_1949_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_1941_, v___x_1948_, v_a_1947_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v_a_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
v_a_1951_ = lean_ctor_get(v___x_1949_, 1);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1949_, 2);
v___x_1952_ = lean_unsigned_to_nat(2u);
v___x_1953_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_1941_, v___x_1952_, v_a_1951_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_a_1955_; lean_object* v___x_1956_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
v_a_1955_ = lean_ctor_get(v___x_1953_, 1);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1953_, 2);
v___x_1956_ = l_Lean_Fmt_fmt(v_a_1946_, v_a_1942_, v_a_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v_a_1958_; lean_object* v___x_1959_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
v_a_1958_ = lean_ctor_get(v___x_1956_, 1);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1956_, 2);
v___x_1959_ = l_Lean_Fmt_fmt(v_a_1950_, v_a_1942_, v_a_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v_a_1961_; lean_object* v___x_1962_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
v_a_1961_ = lean_ctor_get(v___x_1959_, 1);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1959_, 2);
v___x_1962_ = l_Lean_Fmt_fmt(v_a_1954_, v_a_1942_, v_a_1961_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1978_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_a_1964_ = lean_ctor_get(v___x_1962_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1966_ = v___x_1962_;
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1968_ = lean_unsigned_to_nat(3u);
v___x_1969_ = lean_mk_empty_array_with_capacity(v___x_1968_);
v___x_1970_ = lean_array_push(v___x_1969_, v_a_1957_);
v___x_1971_ = lean_array_push(v___x_1970_, v_a_1960_);
v___x_1972_ = lean_array_push(v___x_1971_, v_a_1963_);
v___x_1973_ = ((lean_object*)(l_Lean_Fmt_fmtGrindKeywordFilter___closed__0));
v___x_1974_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1972_, v___x_1973_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1974_);
v___x_1976_ = v___x_1966_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_a_1964_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
else
{
lean_dec(v_a_1960_);
lean_dec(v_a_1957_);
return v___x_1962_;
}
}
else
{
lean_dec(v_a_1957_);
lean_dec(v_a_1954_);
return v___x_1959_;
}
}
else
{
lean_dec(v_a_1954_);
lean_dec(v_a_1950_);
return v___x_1956_;
}
}
else
{
lean_object* v_a_1979_; lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_a_1950_);
lean_dec(v_a_1946_);
v_a_1979_ = lean_ctor_get(v___x_1953_, 0);
v_a_1980_ = lean_ctor_get(v___x_1953_, 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1953_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_inc(v_a_1979_);
lean_dec(v___x_1953_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1979_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1946_);
v_a_1988_ = lean_ctor_get(v___x_1949_, 0);
v_a_1989_ = lean_ctor_get(v___x_1949_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1949_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_inc(v_a_1988_);
lean_dec(v___x_1949_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1988_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
v_a_1997_ = lean_ctor_get(v___x_1945_, 0);
v_a_1998_ = lean_ctor_get(v___x_1945_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1945_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_inc(v_a_1997_);
lean_dec(v___x_1945_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1997_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindWithAnnotateState___boxed(lean_object* v_stx_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Fmt_fmtGrindWithAnnotateState(v_stx_2006_, v_a_2007_, v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_stx_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1(){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2023_ = l_Lean_Fmt_fmtAttribute;
v___x_2024_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__1));
v___x_2025_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___closed__3));
v___x_2026_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindWithAnnotateState___boxed), 3, 0);
v___x_2027_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2023_, v___x_2024_, v___x_2025_, v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1___boxed(lean_object* v_a_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1();
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFail(lean_object* v_x_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2043_; uint8_t v___x_2044_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; 
v___x_2043_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFail___closed__1));
lean_inc(v_x_2040_);
v___x_2044_ = l_Lean_Syntax_isOfKind(v_x_2040_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v_x_2040_);
v___x_2067_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v_a_2042_);
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; lean_object* v_tk_2070_; lean_object* v_msg_x3f_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2069_ = lean_unsigned_to_nat(0u);
v_tk_2070_ = l_Lean_Syntax_getArg(v_x_2040_, v___x_2069_);
v___x_2089_ = lean_unsigned_to_nat(1u);
v___x_2090_ = l_Lean_Syntax_getArg(v_x_2040_, v___x_2089_);
lean_dec(v_x_2040_);
v___x_2091_ = l_Lean_Syntax_isNone(v___x_2090_);
if (v___x_2091_ == 0)
{
uint8_t v___x_2092_; 
lean_inc(v___x_2090_);
v___x_2092_ = l_Lean_Syntax_matchesNull(v___x_2090_, v___x_2089_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec(v___x_2090_);
lean_dec(v_tk_2070_);
v___x_2093_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v_a_2042_);
return v___x_2094_;
}
else
{
lean_object* v_msg_x3f_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v_msg_x3f_2095_ = l_Lean_Syntax_getArg(v___x_2090_, v___x_2069_);
lean_dec(v___x_2090_);
v___x_2096_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFail___closed__3));
lean_inc(v_msg_x3f_2095_);
v___x_2097_ = l_Lean_Syntax_isOfKind(v_msg_x3f_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v_msg_x3f_2095_);
lean_dec(v_tk_2070_);
v___x_2098_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v_a_2042_);
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_msg_x3f_2095_);
v_msg_x3f_2072_ = v___x_2100_;
v___y_2073_ = v_a_2041_;
v___y_2074_ = v_a_2042_;
goto v___jp_2071_;
}
}
}
else
{
lean_object* v___x_2101_; 
lean_dec(v___x_2090_);
v___x_2101_ = lean_box(0);
v_msg_x3f_2072_ = v___x_2101_;
v___y_2073_ = v_a_2041_;
v___y_2074_ = v_a_2042_;
goto v___jp_2071_;
}
v___jp_2071_:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Fmt_fmt(v_tk_2070_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2075_) == 0)
{
if (lean_obj_tag(v_msg_x3f_2072_) == 0)
{
lean_object* v_a_2076_; lean_object* v_a_2077_; lean_object* v___x_2078_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
v_a_2077_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2075_, 2);
v___x_2078_ = lean_box(0);
v___y_2046_ = v_a_2076_;
v___y_2047_ = v_a_2077_;
v___y_2048_ = v___y_2073_;
v___y_2049_ = v___x_2078_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2079_; lean_object* v_a_2080_; lean_object* v_val_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2079_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2079_);
v_a_2080_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2075_, 2);
v_val_2081_ = lean_ctor_get(v_msg_x3f_2072_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_msg_x3f_2072_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v_msg_x3f_2072_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_val_2081_);
lean_dec(v_msg_x3f_2072_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_val_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
v___y_2046_ = v_a_2079_;
v___y_2047_ = v_a_2080_;
v___y_2048_ = v___y_2073_;
v___y_2049_ = v___x_2086_;
goto v___jp_2045_;
}
}
}
}
else
{
lean_dec(v_msg_x3f_2072_);
return v___x_2075_;
}
}
}
v___jp_2045_:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Fmt_fmt_x3f(v___y_2049_, v___y_2048_, v___y_2047_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2066_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_a_2052_ = lean_ctor_get(v___x_2050_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2054_ = v___x_2050_;
v_isShared_2055_ = v_isSharedCheck_2066_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2066_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2056_ = lean_unsigned_to_nat(2u);
v___x_2057_ = lean_mk_empty_array_with_capacity(v___x_2056_);
v___x_2058_ = lean_array_push(v___x_2057_, v___y_2046_);
v___x_2059_ = lean_array_push(v___x_2058_, v_a_2051_);
v___x_2060_ = 0;
v___x_2061_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2061_, 0, v___x_2044_);
lean_ctor_set_uint8(v___x_2061_, 1, v___x_2060_);
lean_ctor_set_uint8(v___x_2061_, 2, v___x_2060_);
lean_ctor_set_uint8(v___x_2061_, 3, v___x_2060_);
v___x_2062_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2059_, v___x_2061_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2062_);
v___x_2064_ = v___x_2054_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_a_2052_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_dec_ref(v___y_2046_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFail___boxed(lean_object* v_x_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Fmt_fmtGrindFail(v_x_2102_, v_a_2103_, v_a_2104_);
lean_dec_ref(v_a_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1(){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2112_ = l_Lean_Fmt_fmtAttribute;
v___x_2113_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFail___closed__1));
v___x_2114_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___closed__1));
v___x_2115_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFail___boxed), 3, 0);
v___x_2116_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2112_, v___x_2113_, v___x_2114_, v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1___boxed(lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1();
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRenameI(lean_object* v_x_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRenameI___closed__1));
lean_inc(v_x_2126_);
v___x_2130_ = l_Lean_Syntax_isOfKind(v_x_2126_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v_x_2126_);
v___x_2131_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v_a_2128_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; lean_object* v_tk_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_unsigned_to_nat(0u);
v_tk_2134_ = l_Lean_Syntax_getArg(v_x_2126_, v___x_2133_);
v___x_2135_ = l_Lean_Fmt_fmt(v_tk_2134_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v_args_2140_; lean_object* v___x_2141_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
v_a_2137_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2135_, 2);
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = l_Lean_Syntax_getArg(v_x_2126_, v___x_2138_);
lean_dec(v_x_2126_);
v_args_2140_ = l_Lean_Syntax_getArgs(v___x_2139_);
lean_dec(v___x_2139_);
v___x_2141_ = l_Lean_Fmt_fmtArray___redArg(v_args_2140_, v_a_2127_, v_a_2137_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2156_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_a_2143_ = lean_ctor_get(v___x_2141_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2145_ = v___x_2141_;
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2147_ = lean_mk_empty_array_with_capacity(v___x_2138_);
v___x_2148_ = lean_array_push(v___x_2147_, v_a_2136_);
v___x_2149_ = l_Array_append___redArg(v___x_2148_, v_a_2142_);
lean_dec(v_a_2142_);
v___x_2150_ = 0;
v___x_2151_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2151_, 0, v___x_2130_);
lean_ctor_set_uint8(v___x_2151_, 1, v___x_2150_);
lean_ctor_set_uint8(v___x_2151_, 2, v___x_2150_);
lean_ctor_set_uint8(v___x_2151_, 3, v___x_2150_);
v___x_2152_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2149_, v___x_2151_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2152_);
v___x_2154_ = v___x_2145_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_a_2143_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_a_2136_);
v_a_2157_ = lean_ctor_get(v___x_2141_, 0);
v_a_2158_ = lean_ctor_get(v___x_2141_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2141_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_inc(v_a_2157_);
lean_dec(v___x_2141_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2157_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_dec(v_x_2126_);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRenameI___boxed(lean_object* v_x_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_Fmt_fmtGrindRenameI(v_x_2166_, v_a_2167_, v_a_2168_);
lean_dec_ref(v_a_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1(){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2176_ = l_Lean_Fmt_fmtAttribute;
v___x_2177_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRenameI___closed__1));
v___x_2178_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___closed__1));
v___x_2179_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindRenameI___boxed), 3, 0);
v___x_2180_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2176_, v___x_2177_, v___x_2178_, v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1___boxed(lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1();
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindApply(lean_object* v_x_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = ((lean_object*)(l_Lean_Fmt_fmtGrindApply___closed__1));
lean_inc(v_x_2190_);
v___x_2194_ = l_Lean_Syntax_isOfKind(v_x_2190_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec(v_x_2190_);
v___x_2195_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v_a_2192_);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v_tk_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_unsigned_to_nat(0u);
v_tk_2198_ = l_Lean_Syntax_getArg(v_x_2190_, v___x_2197_);
v___x_2199_ = l_Lean_Fmt_fmt(v_tk_2198_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
v_a_2201_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2199_, 2);
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = l_Lean_Syntax_getArg(v_x_2190_, v___x_2202_);
lean_dec(v_x_2190_);
v___x_2204_ = l_Lean_Fmt_fmt(v___x_2203_, v_a_2191_, v_a_2201_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2220_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_a_2206_ = lean_ctor_get(v___x_2204_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2208_ = v___x_2204_;
v_isShared_2209_ = v_isSharedCheck_2220_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2220_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2210_ = lean_unsigned_to_nat(2u);
v___x_2211_ = lean_mk_empty_array_with_capacity(v___x_2210_);
v___x_2212_ = lean_array_push(v___x_2211_, v_a_2200_);
v___x_2213_ = lean_array_push(v___x_2212_, v_a_2205_);
v___x_2214_ = 0;
v___x_2215_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2215_, 0, v___x_2194_);
lean_ctor_set_uint8(v___x_2215_, 1, v___x_2214_);
lean_ctor_set_uint8(v___x_2215_, 2, v___x_2214_);
lean_ctor_set_uint8(v___x_2215_, 3, v___x_2214_);
v___x_2216_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2213_, v___x_2215_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2216_);
v___x_2218_ = v___x_2208_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_a_2206_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_dec(v_a_2200_);
return v___x_2204_;
}
}
else
{
lean_dec(v_x_2190_);
return v___x_2199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindApply___boxed(lean_object* v_x_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Fmt_fmtGrindApply(v_x_2221_, v_a_2222_, v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1(){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2231_ = l_Lean_Fmt_fmtAttribute;
v___x_2232_ = ((lean_object*)(l_Lean_Fmt_fmtGrindApply___closed__1));
v___x_2233_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___closed__1));
v___x_2234_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindApply___boxed), 3, 0);
v___x_2235_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2231_, v___x_2232_, v___x_2233_, v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1___boxed(lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1();
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindInternalize(lean_object* v_x_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2248_; uint8_t v___x_2249_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; 
v___x_2248_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInternalize___closed__1));
lean_inc(v_x_2245_);
v___x_2249_ = l_Lean_Syntax_isOfKind(v_x_2245_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v_x_2245_);
v___x_2272_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v_a_2247_);
return v___x_2273_;
}
else
{
lean_object* v___x_2274_; lean_object* v_tk_2275_; lean_object* v_n_x3f_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2274_ = lean_unsigned_to_nat(0u);
v_tk_2275_ = l_Lean_Syntax_getArg(v_x_2245_, v___x_2274_);
v___x_2294_ = lean_unsigned_to_nat(1u);
v___x_2295_ = l_Lean_Syntax_getArg(v_x_2245_, v___x_2294_);
lean_dec(v_x_2245_);
v___x_2296_ = l_Lean_Syntax_isNone(v___x_2295_);
if (v___x_2296_ == 0)
{
uint8_t v___x_2297_; 
lean_inc(v___x_2295_);
v___x_2297_ = l_Lean_Syntax_matchesNull(v___x_2295_, v___x_2294_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec(v___x_2295_);
lean_dec(v_tk_2275_);
v___x_2298_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v_a_2247_);
return v___x_2299_;
}
else
{
lean_object* v_n_x3f_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v_n_x3f_2300_ = l_Lean_Syntax_getArg(v___x_2295_, v___x_2274_);
lean_dec(v___x_2295_);
v___x_2301_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFilterGenLt___closed__3));
lean_inc(v_n_x3f_2300_);
v___x_2302_ = l_Lean_Syntax_isOfKind(v_n_x3f_2300_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec(v_n_x3f_2300_);
lean_dec(v_tk_2275_);
v___x_2303_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v_a_2247_);
return v___x_2304_;
}
else
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_n_x3f_2300_);
v_n_x3f_2277_ = v___x_2305_;
v___y_2278_ = v_a_2246_;
v___y_2279_ = v_a_2247_;
goto v___jp_2276_;
}
}
}
else
{
lean_object* v___x_2306_; 
lean_dec(v___x_2295_);
v___x_2306_ = lean_box(0);
v_n_x3f_2277_ = v___x_2306_;
v___y_2278_ = v_a_2246_;
v___y_2279_ = v_a_2247_;
goto v___jp_2276_;
}
v___jp_2276_:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Fmt_fmt(v_tk_2275_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2280_) == 0)
{
if (lean_obj_tag(v_n_x3f_2277_) == 0)
{
lean_object* v_a_2281_; lean_object* v_a_2282_; lean_object* v___x_2283_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
v_a_2282_ = lean_ctor_get(v___x_2280_, 1);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2280_, 2);
v___x_2283_ = lean_box(0);
v___y_2251_ = v_a_2281_;
v___y_2252_ = v___y_2278_;
v___y_2253_ = v_a_2282_;
v___y_2254_ = v___x_2283_;
goto v___jp_2250_;
}
else
{
lean_object* v_a_2284_; lean_object* v_a_2285_; lean_object* v_val_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
v_a_2284_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2284_);
v_a_2285_ = lean_ctor_get(v___x_2280_, 1);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2280_, 2);
v_val_2286_ = lean_ctor_get(v_n_x3f_2277_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_n_x3f_2277_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v_n_x3f_2277_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_val_2286_);
lean_dec(v_n_x3f_2277_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_val_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
v___y_2251_ = v_a_2284_;
v___y_2252_ = v___y_2278_;
v___y_2253_ = v_a_2285_;
v___y_2254_ = v___x_2291_;
goto v___jp_2250_;
}
}
}
}
else
{
lean_dec(v_n_x3f_2277_);
return v___x_2280_;
}
}
}
v___jp_2250_:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Fmt_fmt_x3f(v___y_2254_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2271_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_a_2257_ = lean_ctor_get(v___x_2255_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2259_ = v___x_2255_;
v_isShared_2260_ = v_isSharedCheck_2271_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2271_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2261_ = lean_unsigned_to_nat(2u);
v___x_2262_ = lean_mk_empty_array_with_capacity(v___x_2261_);
v___x_2263_ = lean_array_push(v___x_2262_, v___y_2251_);
v___x_2264_ = lean_array_push(v___x_2263_, v_a_2256_);
v___x_2265_ = 0;
v___x_2266_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2266_, 0, v___x_2249_);
lean_ctor_set_uint8(v___x_2266_, 1, v___x_2265_);
lean_ctor_set_uint8(v___x_2266_, 2, v___x_2265_);
lean_ctor_set_uint8(v___x_2266_, 3, v___x_2265_);
v___x_2267_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2264_, v___x_2266_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2267_);
v___x_2269_ = v___x_2259_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_a_2257_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_dec_ref(v___y_2251_);
return v___x_2255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindInternalize___boxed(lean_object* v_x_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Fmt_fmtGrindInternalize(v_x_2307_, v_a_2308_, v_a_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1(){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2317_ = l_Lean_Fmt_fmtAttribute;
v___x_2318_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInternalize___closed__1));
v___x_2319_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___closed__1));
v___x_2320_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindInternalize___boxed), 3, 0);
v___x_2321_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2317_, v___x_2318_, v___x_2319_, v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1___boxed(lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1();
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindExact(lean_object* v_x_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = ((lean_object*)(l_Lean_Fmt_fmtGrindExact___closed__1));
lean_inc(v_x_2331_);
v___x_2335_ = l_Lean_Syntax_isOfKind(v_x_2331_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v_x_2331_);
v___x_2336_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v_a_2333_);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v_tk_2339_; lean_object* v___x_2340_; 
v___x_2338_ = lean_unsigned_to_nat(0u);
v_tk_2339_ = l_Lean_Syntax_getArg(v_x_2331_, v___x_2338_);
v___x_2340_ = l_Lean_Fmt_fmt(v_tk_2339_, v_a_2332_, v_a_2333_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
v_a_2342_ = lean_ctor_get(v___x_2340_, 1);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2340_, 2);
v___x_2343_ = lean_unsigned_to_nat(1u);
v___x_2344_ = l_Lean_Syntax_getArg(v_x_2331_, v___x_2343_);
lean_dec(v_x_2331_);
v___x_2345_ = l_Lean_Fmt_fmt(v___x_2344_, v_a_2332_, v_a_2342_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2361_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_a_2347_ = lean_ctor_get(v___x_2345_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2349_ = v___x_2345_;
v_isShared_2350_ = v_isSharedCheck_2361_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2361_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2351_ = lean_unsigned_to_nat(2u);
v___x_2352_ = lean_mk_empty_array_with_capacity(v___x_2351_);
v___x_2353_ = lean_array_push(v___x_2352_, v_a_2341_);
v___x_2354_ = lean_array_push(v___x_2353_, v_a_2346_);
v___x_2355_ = 0;
v___x_2356_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2356_, 0, v___x_2335_);
lean_ctor_set_uint8(v___x_2356_, 1, v___x_2355_);
lean_ctor_set_uint8(v___x_2356_, 2, v___x_2355_);
lean_ctor_set_uint8(v___x_2356_, 3, v___x_2355_);
v___x_2357_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2354_, v___x_2356_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2357_);
v___x_2359_ = v___x_2349_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_a_2347_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_dec(v_a_2341_);
return v___x_2345_;
}
}
else
{
lean_dec(v_x_2331_);
return v___x_2340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindExact___boxed(lean_object* v_x_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Fmt_fmtGrindExact(v_x_2362_, v_a_2363_, v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1(){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2372_ = l_Lean_Fmt_fmtAttribute;
v___x_2373_ = ((lean_object*)(l_Lean_Fmt_fmtGrindExact___closed__1));
v___x_2374_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___closed__1));
v___x_2375_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindExact___boxed), 3, 0);
v___x_2376_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2372_, v___x_2373_, v___x_2374_, v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1___boxed(lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1();
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindInstantiate(lean_object* v_x_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; 
v___x_2392_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__1));
lean_inc(v_x_2389_);
v___x_2393_ = l_Lean_Syntax_isOfKind(v_x_2389_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec(v_x_2389_);
v___x_2441_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v_a_2391_);
return v___x_2442_;
}
else
{
lean_object* v___x_2443_; lean_object* v_tk_2444_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v_lbTk_x3f_2449_; lean_object* v_thms_x3f_2450_; lean_object* v_rbTk_x3f_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___x_2469_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v_approx_x3f_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v_only_x3f_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___x_2443_ = lean_unsigned_to_nat(0u);
v_tk_2444_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2443_);
v___x_2469_ = lean_unsigned_to_nat(1u);
v___x_2503_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2469_);
v___x_2504_ = l_Lean_Syntax_isNone(v___x_2503_);
if (v___x_2504_ == 0)
{
uint8_t v___x_2505_; 
lean_inc(v___x_2503_);
v___x_2505_ = l_Lean_Syntax_matchesNull(v___x_2503_, v___x_2469_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v___x_2503_);
lean_dec(v_tk_2444_);
lean_dec(v_x_2389_);
v___x_2506_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v_a_2391_);
return v___x_2507_;
}
else
{
lean_object* v_only_x3f_2508_; lean_object* v___x_2509_; 
v_only_x3f_2508_ = l_Lean_Syntax_getArg(v___x_2503_, v___x_2443_);
lean_dec(v___x_2503_);
v___x_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_only_x3f_2508_);
v_only_x3f_2491_ = v___x_2509_;
v___y_2492_ = v_a_2390_;
v___y_2493_ = v_a_2391_;
goto v___jp_2490_;
}
}
else
{
lean_object* v___x_2510_; 
lean_dec(v___x_2503_);
v___x_2510_ = lean_box(0);
v_only_x3f_2491_ = v___x_2510_;
v___y_2492_ = v_a_2390_;
v___y_2493_ = v_a_2391_;
goto v___jp_2490_;
}
v___jp_2445_:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_Fmt_fmt(v_tk_2444_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_a_2456_; lean_object* v___x_2457_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
v_a_2456_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2454_, 2);
v___x_2457_ = l_Lean_Fmt_fmt_x3f(v___y_2446_, v___y_2452_, v_a_2456_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
v_a_2459_ = lean_ctor_get(v___x_2457_, 1);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2457_, 2);
v___x_2460_ = l_Lean_Fmt_fmt_x3f(v___y_2448_, v___y_2452_, v_a_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v_a_2462_; lean_object* v___x_2463_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
v_a_2462_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___x_2460_, 2);
v___x_2463_ = l_Lean_Fmt_fmt_x3f(v_lbTk_x3f_2449_, v___y_2452_, v_a_2462_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v_a_2465_; lean_object* v___x_2466_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
v_a_2465_ = lean_ctor_get(v___x_2463_, 1);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2463_, 2);
v___x_2466_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__2));
if (lean_obj_tag(v_thms_x3f_2450_) == 0)
{
lean_object* v___x_2467_; 
v___x_2467_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__3));
v___y_2395_ = v_a_2464_;
v___y_2396_ = v_a_2461_;
v___y_2397_ = v___y_2452_;
v___y_2398_ = v_a_2455_;
v___y_2399_ = v_rbTk_x3f_2451_;
v___y_2400_ = v_a_2465_;
v___y_2401_ = v___y_2447_;
v___y_2402_ = v___x_2466_;
v___y_2403_ = v_a_2458_;
v___y_2404_ = v___x_2467_;
goto v___jp_2394_;
}
else
{
lean_object* v_val_2468_; 
v_val_2468_ = lean_ctor_get(v_thms_x3f_2450_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v_thms_x3f_2450_, 1);
v___y_2395_ = v_a_2464_;
v___y_2396_ = v_a_2461_;
v___y_2397_ = v___y_2452_;
v___y_2398_ = v_a_2455_;
v___y_2399_ = v_rbTk_x3f_2451_;
v___y_2400_ = v_a_2465_;
v___y_2401_ = v___y_2447_;
v___y_2402_ = v___x_2466_;
v___y_2403_ = v_a_2458_;
v___y_2404_ = v_val_2468_;
goto v___jp_2394_;
}
}
else
{
lean_dec(v_a_2461_);
lean_dec(v_a_2458_);
lean_dec(v_a_2455_);
lean_dec(v_rbTk_x3f_2451_);
lean_dec(v_thms_x3f_2450_);
return v___x_2463_;
}
}
else
{
lean_dec(v_a_2458_);
lean_dec(v_a_2455_);
lean_dec(v_rbTk_x3f_2451_);
lean_dec(v_thms_x3f_2450_);
lean_dec(v_lbTk_x3f_2449_);
return v___x_2460_;
}
}
else
{
lean_dec(v_a_2455_);
lean_dec(v_rbTk_x3f_2451_);
lean_dec(v_thms_x3f_2450_);
lean_dec(v_lbTk_x3f_2449_);
lean_dec(v___y_2448_);
return v___x_2457_;
}
}
else
{
lean_dec(v_rbTk_x3f_2451_);
lean_dec(v_thms_x3f_2450_);
lean_dec(v_lbTk_x3f_2449_);
lean_dec(v___y_2448_);
lean_dec(v___y_2446_);
return v___x_2454_;
}
}
v___jp_2470_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2476_ = lean_unsigned_to_nat(3u);
v___x_2477_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2476_);
lean_dec(v_x_2389_);
v___x_2478_ = l_Lean_Syntax_isNone(v___x_2477_);
if (v___x_2478_ == 0)
{
uint8_t v___x_2479_; 
lean_inc(v___x_2477_);
v___x_2479_ = l_Lean_Syntax_matchesNull(v___x_2477_, v___x_2476_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec(v___x_2477_);
lean_dec(v_approx_x3f_2473_);
lean_dec(v___y_2471_);
lean_dec(v_tk_2444_);
v___x_2480_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___y_2475_);
return v___x_2481_;
}
else
{
lean_object* v_lbTk_x3f_2482_; lean_object* v___x_2483_; lean_object* v_rbTk_x3f_2484_; lean_object* v_thms_x3f_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v_lbTk_x3f_2482_ = l_Lean_Syntax_getArg(v___x_2477_, v___x_2443_);
v___x_2483_ = l_Lean_Syntax_getArg(v___x_2477_, v___x_2469_);
v_rbTk_x3f_2484_ = l_Lean_Syntax_getArg(v___x_2477_, v___y_2472_);
lean_dec(v___x_2477_);
v_thms_x3f_2485_ = l_Lean_Syntax_getArgs(v___x_2483_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v_lbTk_x3f_2482_);
v___x_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_thms_x3f_2485_);
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_rbTk_x3f_2484_);
v___y_2446_ = v___y_2471_;
v___y_2447_ = v___y_2472_;
v___y_2448_ = v_approx_x3f_2473_;
v_lbTk_x3f_2449_ = v___x_2486_;
v_thms_x3f_2450_ = v___x_2487_;
v_rbTk_x3f_2451_ = v___x_2488_;
v___y_2452_ = v___y_2474_;
v___y_2453_ = v___y_2475_;
goto v___jp_2445_;
}
}
else
{
lean_object* v___x_2489_; 
lean_dec(v___x_2477_);
v___x_2489_ = lean_box(0);
v___y_2446_ = v___y_2471_;
v___y_2447_ = v___y_2472_;
v___y_2448_ = v_approx_x3f_2473_;
v_lbTk_x3f_2449_ = v___x_2489_;
v_thms_x3f_2450_ = v___x_2489_;
v_rbTk_x3f_2451_ = v___x_2489_;
v___y_2452_ = v___y_2474_;
v___y_2453_ = v___y_2475_;
goto v___jp_2445_;
}
}
v___jp_2490_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2494_ = lean_unsigned_to_nat(2u);
v___x_2495_ = l_Lean_Syntax_getArg(v_x_2389_, v___x_2494_);
v___x_2496_ = l_Lean_Syntax_isNone(v___x_2495_);
if (v___x_2496_ == 0)
{
uint8_t v___x_2497_; 
lean_inc(v___x_2495_);
v___x_2497_ = l_Lean_Syntax_matchesNull(v___x_2495_, v___x_2469_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec(v___x_2495_);
lean_dec(v_only_x3f_2491_);
lean_dec(v_tk_2444_);
lean_dec(v_x_2389_);
v___x_2498_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___y_2493_);
return v___x_2499_;
}
else
{
lean_object* v_approx_x3f_2500_; lean_object* v___x_2501_; 
v_approx_x3f_2500_ = l_Lean_Syntax_getArg(v___x_2495_, v___x_2443_);
lean_dec(v___x_2495_);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_approx_x3f_2500_);
v___y_2471_ = v_only_x3f_2491_;
v___y_2472_ = v___x_2494_;
v_approx_x3f_2473_ = v___x_2501_;
v___y_2474_ = v___y_2492_;
v___y_2475_ = v___y_2493_;
goto v___jp_2470_;
}
}
else
{
lean_object* v___x_2502_; 
lean_dec(v___x_2495_);
v___x_2502_ = lean_box(0);
v___y_2471_ = v_only_x3f_2491_;
v___y_2472_ = v___x_2494_;
v_approx_x3f_2473_ = v___x_2502_;
v___y_2474_ = v___y_2492_;
v___y_2475_ = v___y_2493_;
goto v___jp_2470_;
}
}
}
v___jp_2394_:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_2404_, v___y_2397_, v___y_2400_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v_a_2407_; lean_object* v___x_2408_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
v_a_2407_ = lean_ctor_get(v___x_2405_, 1);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2405_, 2);
v___x_2408_ = l_Lean_Fmt_fmt_x3f(v___y_2399_, v___y_2397_, v_a_2407_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2431_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_a_2410_ = lean_ctor_get(v___x_2408_, 1);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2412_ = v___x_2408_;
v_isShared_2413_ = v_isSharedCheck_2431_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2431_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2414_ = lean_unsigned_to_nat(3u);
v___x_2415_ = lean_mk_empty_array_with_capacity(v___x_2414_);
v___x_2416_ = lean_array_push(v___x_2415_, v___y_2398_);
v___x_2417_ = lean_array_push(v___x_2416_, v___y_2403_);
v___x_2418_ = lean_array_push(v___x_2417_, v___y_2396_);
v___x_2419_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2418_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = 0;
v___x_2421_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2421_, 0, v___x_2420_);
lean_ctor_set_uint8(v___x_2421_, 1, v___x_2393_);
lean_inc_ref(v___y_2402_);
v___x_2422_ = l_Lean_Fmt_Layouts_collection(v___y_2402_, v___y_2395_, v_a_2406_, v_a_2409_, v___x_2421_);
lean_dec(v_a_2406_);
v___x_2423_ = lean_mk_empty_array_with_capacity(v___y_2401_);
v___x_2424_ = lean_array_push(v___x_2423_, v___x_2419_);
v___x_2425_ = lean_array_push(v___x_2424_, v___x_2422_);
v___x_2426_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2426_, 0, v___x_2393_);
lean_ctor_set_uint8(v___x_2426_, 1, v___x_2420_);
lean_ctor_set_uint8(v___x_2426_, 2, v___x_2420_);
lean_ctor_set_uint8(v___x_2426_, 3, v___x_2420_);
v___x_2427_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2425_, v___x_2426_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2427_);
v___x_2429_ = v___x_2412_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_a_2410_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
else
{
lean_dec(v_a_2406_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v___y_2398_);
lean_dec_ref(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v___x_2408_;
}
}
else
{
lean_object* v_a_2432_; lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec_ref(v___y_2396_);
lean_dec_ref(v___y_2395_);
v_a_2432_ = lean_ctor_get(v___x_2405_, 0);
v_a_2433_ = lean_ctor_get(v___x_2405_, 1);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2405_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_inc(v_a_2432_);
lean_dec(v___x_2405_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2432_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindInstantiate___boxed(lean_object* v_x_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Fmt_fmtGrindInstantiate(v_x_2511_, v_a_2512_, v_a_2513_);
lean_dec_ref(v_a_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1(){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2521_ = l_Lean_Fmt_fmtAttribute;
v___x_2522_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__1));
v___x_2523_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___closed__1));
v___x_2524_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindInstantiate___boxed), 3, 0);
v___x_2525_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2521_, v___x_2522_, v___x_2523_, v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1___boxed(lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1();
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindUse(lean_object* v_x_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = ((lean_object*)(l_Lean_Fmt_fmtGrindUse___closed__1));
lean_inc(v_x_2535_);
v___x_2539_ = l_Lean_Syntax_isOfKind(v_x_2535_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_dec(v_x_2535_);
v___x_2540_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v_a_2537_);
return v___x_2541_;
}
else
{
lean_object* v___x_2542_; lean_object* v_tk_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_unsigned_to_nat(0u);
v_tk_2543_ = l_Lean_Syntax_getArg(v_x_2535_, v___x_2542_);
v___x_2544_ = l_Lean_Fmt_fmt(v_tk_2543_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v_lbTk_2548_; lean_object* v___x_2549_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
v_a_2546_ = lean_ctor_get(v___x_2544_, 1);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2544_, 2);
v___x_2547_ = lean_unsigned_to_nat(1u);
v_lbTk_2548_ = l_Lean_Syntax_getArg(v_x_2535_, v___x_2547_);
v___x_2549_ = l_Lean_Fmt_fmt(v_lbTk_2548_, v_a_2536_, v_a_2546_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v_a_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_thms_2554_; lean_object* v___x_2555_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
v_a_2551_ = lean_ctor_get(v___x_2549_, 1);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2549_, 2);
v___x_2552_ = lean_unsigned_to_nat(2u);
v___x_2553_ = l_Lean_Syntax_getArg(v_x_2535_, v___x_2552_);
v_thms_2554_ = l_Lean_Syntax_getArgs(v___x_2553_);
lean_dec(v___x_2553_);
v___x_2555_ = l_Lean_Fmt_fmtTSepArray___redArg(v_thms_2554_, v_a_2536_, v_a_2551_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v_a_2557_; lean_object* v___x_2558_; lean_object* v_rbTk_2559_; lean_object* v___x_2560_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
v_a_2557_ = lean_ctor_get(v___x_2555_, 1);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2555_, 2);
v___x_2558_ = lean_unsigned_to_nat(3u);
v_rbTk_2559_ = l_Lean_Syntax_getArg(v_x_2535_, v___x_2558_);
lean_dec(v_x_2535_);
v___x_2560_ = l_Lean_Fmt_fmt(v_rbTk_2559_, v_a_2536_, v_a_2557_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2578_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_a_2562_ = lean_ctor_get(v___x_2560_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2564_ = v___x_2560_;
v_isShared_2565_ = v_isSharedCheck_2578_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2578_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2566_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__2));
v___x_2567_ = 0;
v___x_2568_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2568_, 0, v___x_2567_);
lean_ctor_set_uint8(v___x_2568_, 1, v___x_2539_);
v___x_2569_ = l_Lean_Fmt_Layouts_collection(v___x_2566_, v_a_2550_, v_a_2556_, v_a_2561_, v___x_2568_);
lean_dec(v_a_2556_);
v___x_2570_ = lean_mk_empty_array_with_capacity(v___x_2552_);
v___x_2571_ = lean_array_push(v___x_2570_, v_a_2545_);
v___x_2572_ = lean_array_push(v___x_2571_, v___x_2569_);
v___x_2573_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2573_, 0, v___x_2539_);
lean_ctor_set_uint8(v___x_2573_, 1, v___x_2567_);
lean_ctor_set_uint8(v___x_2573_, 2, v___x_2567_);
lean_ctor_set_uint8(v___x_2573_, 3, v___x_2567_);
v___x_2574_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2572_, v___x_2573_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2574_);
v___x_2576_ = v___x_2564_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_a_2562_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
else
{
lean_dec(v_a_2556_);
lean_dec(v_a_2550_);
lean_dec(v_a_2545_);
return v___x_2560_;
}
}
else
{
lean_object* v_a_2579_; lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_a_2550_);
lean_dec(v_a_2545_);
lean_dec(v_x_2535_);
v_a_2579_ = lean_ctor_get(v___x_2555_, 0);
v_a_2580_ = lean_ctor_get(v___x_2555_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2555_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_inc(v_a_2579_);
lean_dec(v___x_2555_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2579_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_dec(v_a_2545_);
lean_dec(v_x_2535_);
return v___x_2549_;
}
}
else
{
lean_dec(v_x_2535_);
return v___x_2544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindUse___boxed(lean_object* v_x_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_Fmt_fmtGrindUse(v_x_2588_, v_a_2589_, v_a_2590_);
lean_dec_ref(v_a_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1(){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2598_ = l_Lean_Fmt_fmtAttribute;
v___x_2599_ = ((lean_object*)(l_Lean_Fmt_fmtGrindUse___closed__1));
v___x_2600_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___closed__1));
v___x_2601_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindUse___boxed), 3, 0);
v___x_2602_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2598_, v___x_2599_, v___x_2600_, v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1___boxed(lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1();
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFinish(lean_object* v_x_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFinish___closed__1));
lean_inc(v_x_2612_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v_x_2612_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec(v_x_2612_);
v___x_2617_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v_a_2614_);
return v___x_2618_;
}
else
{
lean_object* v___x_2619_; lean_object* v_tk_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___y_2624_; lean_object* v_lbTk_x3f_2625_; lean_object* v_args_x3f_2626_; lean_object* v_rbTk_x3f_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___x_2644_; lean_object* v_only_x3f_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2619_ = lean_unsigned_to_nat(0u);
v_tk_2620_ = l_Lean_Syntax_getArg(v_x_2612_, v___x_2619_);
v___x_2621_ = lean_unsigned_to_nat(1u);
v___x_2622_ = l_Lean_Syntax_getArg(v_x_2612_, v___x_2621_);
v___x_2644_ = lean_unsigned_to_nat(2u);
v___x_2663_ = l_Lean_Syntax_getArg(v_x_2612_, v___x_2644_);
v___x_2664_ = l_Lean_Syntax_isNone(v___x_2663_);
if (v___x_2664_ == 0)
{
uint8_t v___x_2665_; 
lean_inc(v___x_2663_);
v___x_2665_ = l_Lean_Syntax_matchesNull(v___x_2663_, v___x_2621_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec(v___x_2663_);
lean_dec(v___x_2622_);
lean_dec(v_tk_2620_);
lean_dec(v_x_2612_);
v___x_2666_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
lean_ctor_set(v___x_2667_, 1, v_a_2614_);
return v___x_2667_;
}
else
{
lean_object* v_only_x3f_2668_; lean_object* v___x_2669_; 
v_only_x3f_2668_ = l_Lean_Syntax_getArg(v___x_2663_, v___x_2619_);
lean_dec(v___x_2663_);
v___x_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_only_x3f_2668_);
v_only_x3f_2646_ = v___x_2669_;
v___y_2647_ = v_a_2613_;
v___y_2648_ = v_a_2614_;
goto v___jp_2645_;
}
}
else
{
lean_object* v___x_2670_; 
lean_dec(v___x_2663_);
v___x_2670_ = lean_box(0);
v_only_x3f_2646_ = v___x_2670_;
v___y_2647_ = v_a_2613_;
v___y_2648_ = v_a_2614_;
goto v___jp_2645_;
}
v___jp_2623_:
{
lean_object* v_cfgItems_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_cfgItems_2630_ = l_Lean_Syntax_getArgs(v___x_2622_);
lean_dec(v___x_2622_);
v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2621_);
v___x_2632_ = lean_array_push(v___x_2631_, v_tk_2620_);
v___x_2633_ = lean_box(0);
if (lean_obj_tag(v_args_x3f_2626_) == 0)
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Fmt_fmtSimpLikeWithGenericConfig(v___x_2632_, v_cfgItems_2630_, v___x_2633_, v___y_2624_, v_lbTk_x3f_2625_, v___x_2633_, v_rbTk_x3f_2627_, v___x_2633_, v___y_2628_, v___y_2629_);
return v___x_2634_;
}
else
{
lean_object* v_val_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2643_; 
v_val_2635_ = lean_ctor_get(v_args_x3f_2626_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_args_x3f_2626_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2637_ = v_args_x3f_2626_;
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_val_2635_);
lean_dec(v_args_x3f_2626_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_val_2635_);
v___x_2640_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Fmt_fmtSimpLikeWithGenericConfig(v___x_2632_, v_cfgItems_2630_, v___x_2633_, v___y_2624_, v_lbTk_x3f_2625_, v___x_2640_, v_rbTk_x3f_2627_, v___x_2633_, v___y_2628_, v___y_2629_);
return v___x_2641_;
}
}
}
}
v___jp_2645_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2649_ = lean_unsigned_to_nat(3u);
v___x_2650_ = l_Lean_Syntax_getArg(v_x_2612_, v___x_2649_);
lean_dec(v_x_2612_);
v___x_2651_ = l_Lean_Syntax_isNone(v___x_2650_);
if (v___x_2651_ == 0)
{
uint8_t v___x_2652_; 
lean_inc(v___x_2650_);
v___x_2652_ = l_Lean_Syntax_matchesNull(v___x_2650_, v___x_2649_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v___x_2650_);
lean_dec(v_only_x3f_2646_);
lean_dec(v___x_2622_);
lean_dec(v_tk_2620_);
v___x_2653_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v___y_2648_);
return v___x_2654_;
}
else
{
lean_object* v_lbTk_x3f_2655_; lean_object* v___x_2656_; lean_object* v_rbTk_x3f_2657_; lean_object* v_args_x3f_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_lbTk_x3f_2655_ = l_Lean_Syntax_getArg(v___x_2650_, v___x_2619_);
v___x_2656_ = l_Lean_Syntax_getArg(v___x_2650_, v___x_2621_);
v_rbTk_x3f_2657_ = l_Lean_Syntax_getArg(v___x_2650_, v___x_2644_);
lean_dec(v___x_2650_);
v_args_x3f_2658_ = l_Lean_Syntax_getArgs(v___x_2656_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_lbTk_x3f_2655_);
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_args_x3f_2658_);
v___x_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2661_, 0, v_rbTk_x3f_2657_);
v___y_2624_ = v_only_x3f_2646_;
v_lbTk_x3f_2625_ = v___x_2659_;
v_args_x3f_2626_ = v___x_2660_;
v_rbTk_x3f_2627_ = v___x_2661_;
v___y_2628_ = v___y_2647_;
v___y_2629_ = v___y_2648_;
goto v___jp_2623_;
}
}
else
{
lean_object* v___x_2662_; 
lean_dec(v___x_2650_);
v___x_2662_ = lean_box(0);
v___y_2624_ = v_only_x3f_2646_;
v_lbTk_x3f_2625_ = v___x_2662_;
v_args_x3f_2626_ = v___x_2662_;
v_rbTk_x3f_2627_ = v___x_2662_;
v___y_2628_ = v___y_2647_;
v___y_2629_ = v___y_2648_;
goto v___jp_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFinish___boxed(lean_object* v_x_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_Fmt_fmtGrindFinish(v_x_2671_, v_a_2672_, v_a_2673_);
lean_dec_ref(v_a_2672_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1(){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2681_ = l_Lean_Fmt_fmtAttribute;
v___x_2682_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFinish___closed__1));
v___x_2683_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___closed__1));
v___x_2684_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFinish___boxed), 3, 0);
v___x_2685_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2681_, v___x_2682_, v___x_2683_, v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1___boxed(lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1();
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFinishTrace(lean_object* v_x_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2698_; uint8_t v___x_2699_; 
v___x_2698_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFinishTrace___closed__1));
lean_inc(v_x_2695_);
v___x_2699_ = l_Lean_Syntax_isOfKind(v_x_2695_, v___x_2698_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec(v_x_2695_);
v___x_2700_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v_a_2697_);
return v___x_2701_;
}
else
{
lean_object* v___x_2702_; lean_object* v_tk_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___y_2707_; lean_object* v_lbTk_x3f_2708_; lean_object* v_args_x3f_2709_; lean_object* v_rbTk_x3f_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___x_2727_; lean_object* v_only_x3f_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2702_ = lean_unsigned_to_nat(0u);
v_tk_2703_ = l_Lean_Syntax_getArg(v_x_2695_, v___x_2702_);
v___x_2704_ = lean_unsigned_to_nat(1u);
v___x_2705_ = l_Lean_Syntax_getArg(v_x_2695_, v___x_2704_);
v___x_2727_ = lean_unsigned_to_nat(2u);
v___x_2746_ = l_Lean_Syntax_getArg(v_x_2695_, v___x_2727_);
v___x_2747_ = l_Lean_Syntax_isNone(v___x_2746_);
if (v___x_2747_ == 0)
{
uint8_t v___x_2748_; 
lean_inc(v___x_2746_);
v___x_2748_ = l_Lean_Syntax_matchesNull(v___x_2746_, v___x_2704_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_dec(v___x_2746_);
lean_dec(v___x_2705_);
lean_dec(v_tk_2703_);
lean_dec(v_x_2695_);
v___x_2749_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
lean_ctor_set(v___x_2750_, 1, v_a_2697_);
return v___x_2750_;
}
else
{
lean_object* v_only_x3f_2751_; lean_object* v___x_2752_; 
v_only_x3f_2751_ = l_Lean_Syntax_getArg(v___x_2746_, v___x_2702_);
lean_dec(v___x_2746_);
v___x_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_only_x3f_2751_);
v_only_x3f_2729_ = v___x_2752_;
v___y_2730_ = v_a_2696_;
v___y_2731_ = v_a_2697_;
goto v___jp_2728_;
}
}
else
{
lean_object* v___x_2753_; 
lean_dec(v___x_2746_);
v___x_2753_ = lean_box(0);
v_only_x3f_2729_ = v___x_2753_;
v___y_2730_ = v_a_2696_;
v___y_2731_ = v_a_2697_;
goto v___jp_2728_;
}
v___jp_2706_:
{
lean_object* v_cfgItems_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v_cfgItems_2713_ = l_Lean_Syntax_getArgs(v___x_2705_);
lean_dec(v___x_2705_);
v___x_2714_ = lean_mk_empty_array_with_capacity(v___x_2704_);
v___x_2715_ = lean_array_push(v___x_2714_, v_tk_2703_);
v___x_2716_ = lean_box(0);
if (lean_obj_tag(v_args_x3f_2709_) == 0)
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_Fmt_fmtSimpLikeWithGenericConfig(v___x_2715_, v_cfgItems_2713_, v___x_2716_, v___y_2707_, v_lbTk_x3f_2708_, v___x_2716_, v_rbTk_x3f_2710_, v___x_2716_, v___y_2711_, v___y_2712_);
return v___x_2717_;
}
else
{
lean_object* v_val_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2726_; 
v_val_2718_ = lean_ctor_get(v_args_x3f_2709_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_args_x3f_2709_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2720_ = v_args_x3f_2709_;
v_isShared_2721_ = v_isSharedCheck_2726_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_val_2718_);
lean_dec(v_args_x3f_2709_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2726_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_val_2718_);
v___x_2723_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_Fmt_fmtSimpLikeWithGenericConfig(v___x_2715_, v_cfgItems_2713_, v___x_2716_, v___y_2707_, v_lbTk_x3f_2708_, v___x_2723_, v_rbTk_x3f_2710_, v___x_2716_, v___y_2711_, v___y_2712_);
return v___x_2724_;
}
}
}
}
v___jp_2728_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2732_ = lean_unsigned_to_nat(3u);
v___x_2733_ = l_Lean_Syntax_getArg(v_x_2695_, v___x_2732_);
lean_dec(v_x_2695_);
v___x_2734_ = l_Lean_Syntax_isNone(v___x_2733_);
if (v___x_2734_ == 0)
{
uint8_t v___x_2735_; 
lean_inc(v___x_2733_);
v___x_2735_ = l_Lean_Syntax_matchesNull(v___x_2733_, v___x_2732_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec(v___x_2733_);
lean_dec(v_only_x3f_2729_);
lean_dec(v___x_2705_);
lean_dec(v_tk_2703_);
v___x_2736_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v___y_2731_);
return v___x_2737_;
}
else
{
lean_object* v_lbTk_x3f_2738_; lean_object* v___x_2739_; lean_object* v_rbTk_x3f_2740_; lean_object* v_args_x3f_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v_lbTk_x3f_2738_ = l_Lean_Syntax_getArg(v___x_2733_, v___x_2702_);
v___x_2739_ = l_Lean_Syntax_getArg(v___x_2733_, v___x_2704_);
v_rbTk_x3f_2740_ = l_Lean_Syntax_getArg(v___x_2733_, v___x_2727_);
lean_dec(v___x_2733_);
v_args_x3f_2741_ = l_Lean_Syntax_getArgs(v___x_2739_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_lbTk_x3f_2738_);
v___x_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2743_, 0, v_args_x3f_2741_);
v___x_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2744_, 0, v_rbTk_x3f_2740_);
v___y_2707_ = v_only_x3f_2729_;
v_lbTk_x3f_2708_ = v___x_2742_;
v_args_x3f_2709_ = v___x_2743_;
v_rbTk_x3f_2710_ = v___x_2744_;
v___y_2711_ = v___y_2730_;
v___y_2712_ = v___y_2731_;
goto v___jp_2706_;
}
}
else
{
lean_object* v___x_2745_; 
lean_dec(v___x_2733_);
v___x_2745_ = lean_box(0);
v___y_2707_ = v_only_x3f_2729_;
v_lbTk_x3f_2708_ = v___x_2745_;
v_args_x3f_2709_ = v___x_2745_;
v_rbTk_x3f_2710_ = v___x_2745_;
v___y_2711_ = v___y_2730_;
v___y_2712_ = v___y_2731_;
goto v___jp_2706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFinishTrace___boxed(lean_object* v_x_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Fmt_fmtGrindFinishTrace(v_x_2754_, v_a_2755_, v_a_2756_);
lean_dec_ref(v_a_2755_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1(){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2764_ = l_Lean_Fmt_fmtAttribute;
v___x_2765_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFinishTrace___closed__1));
v___x_2766_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___closed__1));
v___x_2767_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFinishTrace___boxed), 3, 0);
v___x_2768_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2764_, v___x_2765_, v___x_2766_, v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1___boxed(lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1();
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHave(lean_object* v_x_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_Lean_Fmt_fmtGrindHave___closed__1));
lean_inc(v_x_2785_);
v___x_2789_ = l_Lean_Syntax_isOfKind(v_x_2785_, v___x_2788_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec(v_x_2785_);
v___x_2790_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v_a_2787_);
return v___x_2791_;
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2792_ = lean_unsigned_to_nat(1u);
v___x_2793_ = l_Lean_Syntax_getArg(v_x_2785_, v___x_2792_);
v___x_2794_ = ((lean_object*)(l_Lean_Fmt_fmtGrindHave___closed__4));
lean_inc(v___x_2793_);
v___x_2795_ = l_Lean_Syntax_isOfKind(v___x_2793_, v___x_2794_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_dec(v___x_2793_);
lean_dec(v_x_2785_);
v___x_2796_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v_a_2787_);
return v___x_2797_;
}
else
{
lean_object* v___x_2798_; lean_object* v_haveTk_2799_; lean_object* v___x_2800_; 
v___x_2798_ = lean_unsigned_to_nat(0u);
v_haveTk_2799_ = l_Lean_Syntax_getArg(v_x_2785_, v___x_2798_);
lean_dec(v_x_2785_);
v___x_2800_ = l_Lean_Fmt_fmt(v_haveTk_2799_, v_a_2786_, v_a_2787_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v_a_2802_; lean_object* v___x_2803_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
v_a_2802_ = lean_ctor_get(v___x_2800_, 1);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2800_, 2);
v___x_2803_ = l_Lean_Fmt_fmt(v___x_2793_, v_a_2786_, v_a_2802_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2815_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_a_2805_ = lean_ctor_get(v___x_2803_, 1);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2807_ = v___x_2803_;
v_isShared_2808_ = v_isSharedCheck_2815_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2815_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2809_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_2810_ = 0;
v___x_2811_ = l_Lean_Fmt_Layouts_letDecl(v_a_2801_, v___x_2809_, v_a_2804_, v___x_2810_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2811_);
v___x_2813_ = v___x_2807_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_a_2805_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_dec(v_a_2801_);
return v___x_2803_;
}
}
else
{
lean_dec(v___x_2793_);
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHave___boxed(lean_object* v_x_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Fmt_fmtGrindHave(v_x_2816_, v_a_2817_, v_a_2818_);
lean_dec_ref(v_a_2817_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1(){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2826_ = l_Lean_Fmt_fmtAttribute;
v___x_2827_ = ((lean_object*)(l_Lean_Fmt_fmtGrindHave___closed__1));
v___x_2828_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___closed__1));
v___x_2829_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindHave___boxed), 3, 0);
v___x_2830_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2826_, v___x_2827_, v___x_2828_, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1___boxed(lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1();
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHaveSilent(lean_object* v_x_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = ((lean_object*)(l_Lean_Fmt_fmtGrindHaveSilent___closed__1));
lean_inc(v_x_2842_);
v___x_2846_ = l_Lean_Syntax_isOfKind(v_x_2842_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec(v_x_2842_);
v___x_2847_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v_a_2844_);
return v___x_2848_;
}
else
{
lean_object* v___x_2849_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v_haveTk_2879_; lean_object* v_id_x3f_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2849_ = lean_unsigned_to_nat(0u);
v_haveTk_2879_ = l_Lean_Syntax_getArg(v_x_2842_, v___x_2849_);
v___x_2900_ = lean_unsigned_to_nat(1u);
v___x_2901_ = l_Lean_Syntax_getArg(v_x_2842_, v___x_2900_);
v___x_2902_ = l_Lean_Syntax_isNone(v___x_2901_);
if (v___x_2902_ == 0)
{
uint8_t v___x_2903_; 
lean_inc(v___x_2901_);
v___x_2903_ = l_Lean_Syntax_matchesNull(v___x_2901_, v___x_2900_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
lean_dec(v___x_2901_);
lean_dec(v_haveTk_2879_);
lean_dec(v_x_2842_);
v___x_2904_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
lean_ctor_set(v___x_2905_, 1, v_a_2844_);
return v___x_2905_;
}
else
{
lean_object* v_id_x3f_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_id_x3f_2906_ = l_Lean_Syntax_getArg(v___x_2901_, v___x_2849_);
lean_dec(v___x_2901_);
v___x_2907_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__3));
lean_inc(v_id_x3f_2906_);
v___x_2908_ = l_Lean_Syntax_isOfKind(v_id_x3f_2906_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec(v_id_x3f_2906_);
lean_dec(v_haveTk_2879_);
lean_dec(v_x_2842_);
v___x_2909_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v_a_2844_);
return v___x_2910_;
}
else
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2911_, 0, v_id_x3f_2906_);
v_id_x3f_2881_ = v___x_2911_;
v___y_2882_ = v_a_2843_;
v___y_2883_ = v_a_2844_;
goto v___jp_2880_;
}
}
}
else
{
lean_object* v___x_2912_; 
lean_dec(v___x_2901_);
v___x_2912_ = lean_box(0);
v_id_x3f_2881_ = v___x_2912_;
v___y_2882_ = v_a_2843_;
v___y_2883_ = v_a_2844_;
goto v___jp_2880_;
}
v___jp_2850_:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_Fmt_fmt_x3f(v___y_2857_, v___y_2852_, v___y_2855_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
v_a_2860_ = lean_ctor_get(v___x_2858_, 1);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2858_, 2);
v___x_2861_ = l_Lean_Fmt_fmt(v___y_2851_, v___y_2852_, v_a_2860_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
v_a_2863_ = lean_ctor_get(v___x_2861_, 1);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2861_, 2);
v___x_2864_ = l_Lean_Fmt_fmt(v___y_2854_, v___y_2852_, v_a_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2878_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_a_2866_ = lean_ctor_get(v___x_2864_, 1);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2868_ = v___x_2864_;
v_isShared_2869_ = v_isSharedCheck_2878_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2878_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2870_ = lean_mk_empty_array_with_capacity(v___y_2856_);
v___x_2871_ = lean_array_push(v___x_2870_, v___y_2853_);
v___x_2872_ = lean_array_push(v___x_2871_, v_a_2859_);
v___x_2873_ = ((lean_object*)(l_Lean_Fmt_fmtGrindHaveSilent___closed__2));
v___x_2874_ = l_Lean_Fmt_Layouts_localSignature(v___x_2872_, v___x_2873_, v_a_2862_, v_a_2865_);
lean_dec_ref(v___x_2872_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2874_);
v___x_2876_ = v___x_2868_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_a_2866_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_dec(v_a_2862_);
lean_dec(v_a_2859_);
lean_dec_ref(v___y_2853_);
return v___x_2864_;
}
}
else
{
lean_dec(v_a_2859_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
return v___x_2861_;
}
}
else
{
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2851_);
return v___x_2858_;
}
}
v___jp_2880_:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_Fmt_fmt(v_haveTk_2879_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v_colonTk_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
v_a_2886_ = lean_ctor_get(v___x_2884_, 1);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2884_, 2);
v___x_2887_ = lean_unsigned_to_nat(2u);
v_colonTk_2888_ = l_Lean_Syntax_getArg(v_x_2842_, v___x_2887_);
v___x_2889_ = lean_unsigned_to_nat(3u);
v___x_2890_ = l_Lean_Syntax_getArg(v_x_2842_, v___x_2889_);
lean_dec(v_x_2842_);
if (lean_obj_tag(v_id_x3f_2881_) == 0)
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_box(0);
v___y_2851_ = v_colonTk_2888_;
v___y_2852_ = v___y_2882_;
v___y_2853_ = v_a_2885_;
v___y_2854_ = v___x_2890_;
v___y_2855_ = v_a_2886_;
v___y_2856_ = v___x_2887_;
v___y_2857_ = v___x_2891_;
goto v___jp_2850_;
}
else
{
lean_object* v_val_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v_val_2892_ = lean_ctor_get(v_id_x3f_2881_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_id_x3f_2881_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v_id_x3f_2881_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_val_2892_);
lean_dec(v_id_x3f_2881_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_val_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
v___y_2851_ = v_colonTk_2888_;
v___y_2852_ = v___y_2882_;
v___y_2853_ = v_a_2885_;
v___y_2854_ = v___x_2890_;
v___y_2855_ = v_a_2886_;
v___y_2856_ = v___x_2887_;
v___y_2857_ = v___x_2897_;
goto v___jp_2850_;
}
}
}
}
else
{
lean_dec(v_id_x3f_2881_);
lean_dec(v_x_2842_);
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHaveSilent___boxed(lean_object* v_x_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Fmt_fmtGrindHaveSilent(v_x_2913_, v_a_2914_, v_a_2915_);
lean_dec_ref(v_a_2914_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1(){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2923_ = l_Lean_Fmt_fmtAttribute;
v___x_2924_ = ((lean_object*)(l_Lean_Fmt_fmtGrindHaveSilent___closed__1));
v___x_2925_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___closed__1));
v___x_2926_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindHaveSilent___boxed), 3, 0);
v___x_2927_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2923_, v___x_2924_, v___x_2925_, v___x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1___boxed(lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1();
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNestedTacticCore(lean_object* v_x_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1));
lean_inc(v_x_2943_);
v___x_2947_ = l_Lean_Syntax_isOfKind(v_x_2943_, v___x_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
lean_dec(v_x_2943_);
v___x_2948_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v_a_2945_);
return v___x_2949_;
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2950_ = lean_unsigned_to_nat(2u);
v___x_2951_ = l_Lean_Syntax_getArg(v_x_2943_, v___x_2950_);
v___x_2952_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNestedTacticCore___closed__3));
lean_inc(v___x_2951_);
v___x_2953_ = l_Lean_Syntax_isOfKind(v___x_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec(v___x_2951_);
lean_dec(v_x_2943_);
v___x_2954_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v_a_2945_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; lean_object* v_tacticTk_2957_; lean_object* v___x_2958_; 
v___x_2956_ = lean_unsigned_to_nat(0u);
v_tacticTk_2957_ = l_Lean_Syntax_getArg(v_x_2943_, v___x_2956_);
v___x_2958_ = l_Lean_Fmt_fmt(v_tacticTk_2957_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v_a_2960_; lean_object* v___x_2961_; lean_object* v_arrowTk_2962_; lean_object* v___x_2963_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
v_a_2960_ = lean_ctor_get(v___x_2958_, 1);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2958_, 2);
v___x_2961_ = lean_unsigned_to_nat(1u);
v_arrowTk_2962_ = l_Lean_Syntax_getArg(v_x_2943_, v___x_2961_);
lean_dec(v_x_2943_);
v___x_2963_ = l_Lean_Fmt_fmt(v_arrowTk_2962_, v_a_2944_, v_a_2960_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v_a_2965_; lean_object* v___x_2966_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
v_a_2965_ = lean_ctor_get(v___x_2963_, 1);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2963_, 2);
v___x_2966_ = l_Lean_Fmt_fmt(v___x_2951_, v_a_2944_, v_a_2965_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2977_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_a_2968_ = lean_ctor_get(v___x_2966_, 1);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2970_ = v___x_2966_;
v_isShared_2971_ = v_isSharedCheck_2977_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2977_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint8_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2972_ = 0;
v___x_2973_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_2959_, v_a_2964_, v_a_2967_, v___x_2972_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2973_);
v___x_2975_ = v___x_2970_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_a_2968_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_dec(v_a_2964_);
lean_dec(v_a_2959_);
return v___x_2966_;
}
}
else
{
lean_dec(v_a_2959_);
lean_dec(v___x_2951_);
return v___x_2963_;
}
}
else
{
lean_dec(v___x_2951_);
lean_dec(v_x_2943_);
return v___x_2958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNestedTacticCore___boxed(lean_object* v_x_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_Fmt_fmtGrindNestedTacticCore(v_x_2978_, v_a_2979_, v_a_2980_);
lean_dec_ref(v_a_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1(){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2988_ = l_Lean_Fmt_fmtAttribute;
v___x_2989_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNestedTacticCore___closed__1));
v___x_2990_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___closed__1));
v___x_2991_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindNestedTacticCore___boxed), 3, 0);
v___x_2992_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2988_, v___x_2989_, v___x_2990_, v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1___boxed(lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1();
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAllGoals(lean_object* v_x_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAllGoals___closed__1));
lean_inc(v_x_3002_);
v___x_3006_ = l_Lean_Syntax_isOfKind(v_x_3002_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec(v_x_3002_);
v___x_3007_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v_a_3004_);
return v___x_3008_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3009_ = lean_unsigned_to_nat(1u);
v___x_3010_ = l_Lean_Syntax_getArg(v_x_3002_, v___x_3009_);
v___x_3011_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3010_);
v___x_3012_ = l_Lean_Syntax_isOfKind(v___x_3010_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec(v___x_3010_);
lean_dec(v_x_3002_);
v___x_3013_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
lean_ctor_set(v___x_3014_, 1, v_a_3004_);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; lean_object* v_tk_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_unsigned_to_nat(0u);
v_tk_3016_ = l_Lean_Syntax_getArg(v_x_3002_, v___x_3015_);
lean_dec(v_x_3002_);
v___x_3017_ = l_Lean_Fmt_fmt(v_tk_3016_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v_a_3019_; lean_object* v___x_3020_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
v_a_3019_ = lean_ctor_get(v___x_3017_, 1);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3017_, 2);
v___x_3020_ = l_Lean_Fmt_fmt(v___x_3010_, v_a_3003_, v_a_3019_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3031_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_a_3022_ = lean_ctor_get(v___x_3020_, 1);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3024_ = v___x_3020_;
v_isShared_3025_ = v_isSharedCheck_3031_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3031_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
uint8_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3026_ = 1;
v___x_3027_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_3018_, v_a_3021_, v___x_3026_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3027_);
v___x_3029_ = v___x_3024_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_a_3022_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
else
{
lean_dec(v_a_3018_);
return v___x_3020_;
}
}
else
{
lean_dec(v___x_3010_);
return v___x_3017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAllGoals___boxed(lean_object* v_x_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_Fmt_fmtGrindAllGoals(v_x_3032_, v_a_3033_, v_a_3034_);
lean_dec_ref(v_a_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1(){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3042_ = l_Lean_Fmt_fmtAttribute;
v___x_3043_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAllGoals___closed__1));
v___x_3044_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___closed__1));
v___x_3045_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindAllGoals___boxed), 3, 0);
v___x_3046_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3042_, v___x_3043_, v___x_3044_, v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1___boxed(lean_object* v_a_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1();
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCase(lean_object* v_x_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_Fmt_fmtGrindCase___closed__1));
lean_inc(v_x_3056_);
v___x_3060_ = l_Lean_Syntax_isOfKind(v_x_3056_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec(v_x_3056_);
v___x_3061_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
lean_ctor_set(v___x_3062_, 1, v_a_3058_);
return v___x_3062_;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3063_ = lean_unsigned_to_nat(3u);
v___x_3064_ = l_Lean_Syntax_getArg(v_x_3056_, v___x_3063_);
v___x_3065_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3064_);
v___x_3066_ = l_Lean_Syntax_isOfKind(v___x_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec(v___x_3064_);
lean_dec(v_x_3056_);
v___x_3067_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v_a_3058_);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; lean_object* v_caseTk_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_arrowTk_3074_; lean_object* v_args_3075_; lean_object* v___x_3076_; 
v___x_3069_ = lean_unsigned_to_nat(0u);
v_caseTk_3070_ = l_Lean_Syntax_getArg(v_x_3056_, v___x_3069_);
v___x_3071_ = lean_unsigned_to_nat(1u);
v___x_3072_ = l_Lean_Syntax_getArg(v_x_3056_, v___x_3071_);
v___x_3073_ = lean_unsigned_to_nat(2u);
v_arrowTk_3074_ = l_Lean_Syntax_getArg(v_x_3056_, v___x_3073_);
lean_dec(v_x_3056_);
v_args_3075_ = l_Lean_Syntax_getArgs(v___x_3072_);
lean_dec(v___x_3072_);
v___x_3076_ = l_Lean_Fmt_fmtCaseDeclaration___redArg(v_caseTk_3070_, v_args_3075_, v_arrowTk_3074_, v___x_3064_, v_a_3057_, v_a_3058_);
return v___x_3076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCase___boxed(lean_object* v_x_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_Fmt_fmtGrindCase(v_x_3077_, v_a_3078_, v_a_3079_);
lean_dec_ref(v_a_3078_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1(){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3087_ = l_Lean_Fmt_fmtAttribute;
v___x_3088_ = ((lean_object*)(l_Lean_Fmt_fmtGrindCase___closed__1));
v___x_3089_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___closed__1));
v___x_3090_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindCase___boxed), 3, 0);
v___x_3091_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3087_, v___x_3088_, v___x_3089_, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1___boxed(lean_object* v_a_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1();
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnyGoals(lean_object* v_x_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3104_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnyGoals___closed__1));
lean_inc(v_x_3101_);
v___x_3105_ = l_Lean_Syntax_isOfKind(v_x_3101_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_dec(v_x_3101_);
v___x_3106_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v_a_3103_);
return v___x_3107_;
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3108_ = lean_unsigned_to_nat(1u);
v___x_3109_ = l_Lean_Syntax_getArg(v_x_3101_, v___x_3108_);
v___x_3110_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3109_);
v___x_3111_ = l_Lean_Syntax_isOfKind(v___x_3109_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec(v___x_3109_);
lean_dec(v_x_3101_);
v___x_3112_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set(v___x_3113_, 1, v_a_3103_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; lean_object* v_tk_3115_; lean_object* v___x_3116_; 
v___x_3114_ = lean_unsigned_to_nat(0u);
v_tk_3115_ = l_Lean_Syntax_getArg(v_x_3101_, v___x_3114_);
lean_dec(v_x_3101_);
v___x_3116_ = l_Lean_Fmt_fmt(v_tk_3115_, v_a_3102_, v_a_3103_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v_a_3118_; lean_object* v___x_3119_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
v_a_3118_ = lean_ctor_get(v___x_3116_, 1);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3116_, 2);
v___x_3119_ = l_Lean_Fmt_fmt(v___x_3109_, v_a_3102_, v_a_3118_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3130_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
v_a_3121_ = lean_ctor_get(v___x_3119_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3123_ = v___x_3119_;
v_isShared_3124_ = v_isSharedCheck_3130_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_inc(v_a_3120_);
lean_dec(v___x_3119_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3130_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3125_ = 1;
v___x_3126_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_3117_, v_a_3120_, v___x_3125_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3126_);
v___x_3128_ = v___x_3123_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_a_3121_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
lean_dec(v_a_3117_);
return v___x_3119_;
}
}
else
{
lean_dec(v___x_3109_);
return v___x_3116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnyGoals___boxed(lean_object* v_x_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Fmt_fmtGrindAnyGoals(v_x_3131_, v_a_3132_, v_a_3133_);
lean_dec_ref(v_a_3132_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1(){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3141_ = l_Lean_Fmt_fmtAttribute;
v___x_3142_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnyGoals___closed__1));
v___x_3143_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___closed__1));
v___x_3144_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindAnyGoals___boxed), 3, 0);
v___x_3145_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3141_, v___x_3142_, v___x_3143_, v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1___boxed(lean_object* v_a_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1();
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFocus(lean_object* v_x_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3158_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFocus___closed__1));
lean_inc(v_x_3155_);
v___x_3159_ = l_Lean_Syntax_isOfKind(v_x_3155_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_dec(v_x_3155_);
v___x_3160_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v_a_3157_);
return v___x_3161_;
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3162_ = lean_unsigned_to_nat(1u);
v___x_3163_ = l_Lean_Syntax_getArg(v_x_3155_, v___x_3162_);
v___x_3164_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3163_);
v___x_3165_ = l_Lean_Syntax_isOfKind(v___x_3163_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec(v___x_3163_);
lean_dec(v_x_3155_);
v___x_3166_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v_a_3157_);
return v___x_3167_;
}
else
{
lean_object* v___x_3168_; lean_object* v_tk_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_unsigned_to_nat(0u);
v_tk_3169_ = l_Lean_Syntax_getArg(v_x_3155_, v___x_3168_);
lean_dec(v_x_3155_);
v___x_3170_ = l_Lean_Fmt_fmt(v_tk_3169_, v_a_3156_, v_a_3157_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v_a_3172_; lean_object* v___x_3173_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
v_a_3172_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_a_3172_);
lean_dec_ref_known(v___x_3170_, 2);
v___x_3173_ = l_Lean_Fmt_fmt(v___x_3163_, v_a_3156_, v_a_3172_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3184_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_a_3175_ = lean_ctor_get(v___x_3173_, 1);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3177_ = v___x_3173_;
v_isShared_3178_ = v_isSharedCheck_3184_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3184_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
uint8_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3179_ = 1;
v___x_3180_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_3171_, v_a_3174_, v___x_3179_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3180_);
v___x_3182_ = v___x_3177_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_a_3175_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
else
{
lean_dec(v_a_3171_);
return v___x_3173_;
}
}
else
{
lean_dec(v___x_3163_);
return v___x_3170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFocus___boxed(lean_object* v_x_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_Fmt_fmtGrindFocus(v_x_3185_, v_a_3186_, v_a_3187_);
lean_dec_ref(v_a_3186_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1(){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3195_ = l_Lean_Fmt_fmtAttribute;
v___x_3196_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFocus___closed__1));
v___x_3197_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___closed__1));
v___x_3198_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFocus___boxed), 3, 0);
v___x_3199_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3195_, v___x_3196_, v___x_3197_, v___x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1___boxed(lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1();
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFailIfSuccess(lean_object* v_x_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3212_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1));
lean_inc(v_x_3209_);
v___x_3213_ = l_Lean_Syntax_isOfKind(v_x_3209_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_dec(v_x_3209_);
v___x_3214_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v_a_3211_);
return v___x_3215_;
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3216_ = lean_unsigned_to_nat(1u);
v___x_3217_ = l_Lean_Syntax_getArg(v_x_3209_, v___x_3216_);
v___x_3218_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3217_);
v___x_3219_ = l_Lean_Syntax_isOfKind(v___x_3217_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec(v___x_3217_);
lean_dec(v_x_3209_);
v___x_3220_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v_a_3211_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; lean_object* v_tk_3223_; lean_object* v___x_3224_; 
v___x_3222_ = lean_unsigned_to_nat(0u);
v_tk_3223_ = l_Lean_Syntax_getArg(v_x_3209_, v___x_3222_);
lean_dec(v_x_3209_);
v___x_3224_ = l_Lean_Fmt_fmt(v_tk_3223_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v_a_3226_; lean_object* v___x_3227_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
v_a_3226_ = lean_ctor_get(v___x_3224_, 1);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3224_, 2);
v___x_3227_ = l_Lean_Fmt_fmt(v___x_3217_, v_a_3210_, v_a_3226_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3238_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_a_3229_ = lean_ctor_get(v___x_3227_, 1);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3231_ = v___x_3227_;
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
uint8_t v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3233_ = 1;
v___x_3234_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_3225_, v_a_3228_, v___x_3233_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3234_);
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v_a_3229_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
else
{
lean_dec(v_a_3225_);
return v___x_3227_;
}
}
else
{
lean_dec(v___x_3217_);
return v___x_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFailIfSuccess___boxed(lean_object* v_x_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Fmt_fmtGrindFailIfSuccess(v_x_3239_, v_a_3240_, v_a_3241_);
lean_dec_ref(v_a_3240_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1(){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3249_ = l_Lean_Fmt_fmtAttribute;
v___x_3250_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFailIfSuccess___closed__1));
v___x_3251_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___closed__1));
v___x_3252_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFailIfSuccess___boxed), 3, 0);
v___x_3253_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3249_, v___x_3250_, v___x_3251_, v___x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1___boxed(lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1();
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTry(lean_object* v_x_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTry___closed__1));
lean_inc(v_x_3263_);
v___x_3267_ = l_Lean_Syntax_isOfKind(v_x_3263_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_dec(v_x_3263_);
v___x_3268_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
lean_ctor_set(v___x_3269_, 1, v_a_3265_);
return v___x_3269_;
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3270_ = lean_unsigned_to_nat(1u);
v___x_3271_ = l_Lean_Syntax_getArg(v_x_3263_, v___x_3270_);
v___x_3272_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3271_);
v___x_3273_ = l_Lean_Syntax_isOfKind(v___x_3271_, v___x_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v___x_3271_);
lean_dec(v_x_3263_);
v___x_3274_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v_a_3265_);
return v___x_3275_;
}
else
{
lean_object* v___x_3276_; lean_object* v_tk_3277_; lean_object* v___x_3278_; 
v___x_3276_ = lean_unsigned_to_nat(0u);
v_tk_3277_ = l_Lean_Syntax_getArg(v_x_3263_, v___x_3276_);
lean_dec(v_x_3263_);
v___x_3278_ = l_Lean_Fmt_fmt(v_tk_3277_, v_a_3264_, v_a_3265_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v_a_3280_; lean_object* v___x_3281_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
v_a_3280_ = lean_ctor_get(v___x_3278_, 1);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3278_, 2);
v___x_3281_ = l_Lean_Fmt_fmt(v___x_3271_, v_a_3264_, v_a_3280_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3292_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_a_3283_ = lean_ctor_get(v___x_3281_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3285_ = v___x_3281_;
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
uint8_t v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3287_ = 1;
v___x_3288_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_3279_, v_a_3282_, v___x_3287_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3288_);
v___x_3290_ = v___x_3285_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_a_3283_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
lean_dec(v_a_3279_);
return v___x_3281_;
}
}
else
{
lean_dec(v___x_3271_);
return v___x_3278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTry___boxed(lean_object* v_x_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Fmt_fmtGrindTry(v_x_3293_, v_a_3294_, v_a_3295_);
lean_dec_ref(v_a_3294_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1(){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3303_ = l_Lean_Fmt_fmtAttribute;
v___x_3304_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTry___closed__1));
v___x_3305_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___closed__1));
v___x_3306_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindTry___boxed), 3, 0);
v___x_3307_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3303_, v___x_3304_, v___x_3305_, v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1___boxed(lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1();
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRepeat(lean_object* v_x_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRepeat___closed__1));
lean_inc(v_x_3317_);
v___x_3321_ = l_Lean_Syntax_isOfKind(v_x_3317_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec(v_x_3317_);
v___x_3322_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
lean_ctor_set(v___x_3323_, 1, v_a_3319_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3324_ = lean_unsigned_to_nat(1u);
v___x_3325_ = l_Lean_Syntax_getArg(v_x_3317_, v___x_3324_);
v___x_3326_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3325_);
v___x_3327_ = l_Lean_Syntax_isOfKind(v___x_3325_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec(v___x_3325_);
lean_dec(v_x_3317_);
v___x_3328_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v_a_3319_);
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; lean_object* v_tk_3331_; lean_object* v___x_3332_; 
v___x_3330_ = lean_unsigned_to_nat(0u);
v_tk_3331_ = l_Lean_Syntax_getArg(v_x_3317_, v___x_3330_);
lean_dec(v_x_3317_);
v___x_3332_ = l_Lean_Fmt_fmt(v_tk_3331_, v_a_3318_, v_a_3319_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v_a_3334_; lean_object* v___x_3335_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
v_a_3334_ = lean_ctor_get(v___x_3332_, 1);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3332_, 2);
v___x_3335_ = l_Lean_Fmt_fmt(v___x_3325_, v_a_3318_, v_a_3334_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3346_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_a_3337_ = lean_ctor_get(v___x_3335_, 1);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3339_ = v___x_3335_;
v_isShared_3340_ = v_isSharedCheck_3346_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3346_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
uint8_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3341_ = 1;
v___x_3342_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_3333_, v_a_3336_, v___x_3341_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3342_);
v___x_3344_ = v___x_3339_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_a_3337_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
else
{
lean_dec(v_a_3333_);
return v___x_3335_;
}
}
else
{
lean_dec(v___x_3325_);
return v___x_3332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRepeat___boxed(lean_object* v_x_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Fmt_fmtGrindRepeat(v_x_3347_, v_a_3348_, v_a_3349_);
lean_dec_ref(v_a_3348_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1(){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3357_ = l_Lean_Fmt_fmtAttribute;
v___x_3358_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRepeat___closed__1));
v___x_3359_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___closed__1));
v___x_3360_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindRepeat___boxed), 3, 0);
v___x_3361_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3357_, v___x_3358_, v___x_3359_, v___x_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1___boxed(lean_object* v_a_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1();
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNext(lean_object* v_x_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNext___closed__1));
lean_inc(v_x_3371_);
v___x_3375_ = l_Lean_Syntax_isOfKind(v_x_3371_, v___x_3374_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec(v_x_3371_);
v___x_3376_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v_a_3373_);
return v___x_3377_;
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3378_ = lean_unsigned_to_nat(3u);
v___x_3379_ = l_Lean_Syntax_getArg(v_x_3371_, v___x_3378_);
v___x_3380_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3379_);
v___x_3381_ = l_Lean_Syntax_isOfKind(v___x_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
lean_dec(v___x_3379_);
lean_dec(v_x_3371_);
v___x_3382_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
lean_ctor_set(v___x_3383_, 1, v_a_3373_);
return v___x_3383_;
}
else
{
lean_object* v___x_3384_; lean_object* v_nextTk_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v_arrowTk_3389_; lean_object* v_args_3390_; lean_object* v___x_3391_; 
v___x_3384_ = lean_unsigned_to_nat(0u);
v_nextTk_3385_ = l_Lean_Syntax_getArg(v_x_3371_, v___x_3384_);
v___x_3386_ = lean_unsigned_to_nat(1u);
v___x_3387_ = l_Lean_Syntax_getArg(v_x_3371_, v___x_3386_);
v___x_3388_ = lean_unsigned_to_nat(2u);
v_arrowTk_3389_ = l_Lean_Syntax_getArg(v_x_3371_, v___x_3388_);
lean_dec(v_x_3371_);
v_args_3390_ = l_Lean_Syntax_getArgs(v___x_3387_);
lean_dec(v___x_3387_);
v___x_3391_ = l_Lean_Fmt_fmtNextLike___redArg(v_nextTk_3385_, v_args_3390_, v_arrowTk_3389_, v___x_3379_, v_a_3372_, v_a_3373_);
return v___x_3391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNext___boxed(lean_object* v_x_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Fmt_fmtGrindNext(v_x_3392_, v_a_3393_, v_a_3394_);
lean_dec_ref(v_a_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1(){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3402_ = l_Lean_Fmt_fmtAttribute;
v___x_3403_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNext___closed__1));
v___x_3404_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___closed__1));
v___x_3405_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindNext___boxed), 3, 0);
v___x_3406_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3402_, v___x_3403_, v___x_3404_, v___x_3405_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1___boxed(lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1();
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDot(lean_object* v_x_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDot___closed__1));
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
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3423_ = lean_unsigned_to_nat(1u);
v___x_3424_ = l_Lean_Syntax_getArg(v_x_3416_, v___x_3423_);
v___x_3425_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3424_);
v___x_3426_ = l_Lean_Syntax_isOfKind(v___x_3424_, v___x_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_dec(v___x_3424_);
lean_dec(v_x_3416_);
v___x_3427_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v_a_3418_);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; lean_object* v_dotTk_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_unsigned_to_nat(0u);
v_dotTk_3430_ = l_Lean_Syntax_getArg(v_x_3416_, v___x_3429_);
lean_dec(v_x_3416_);
v___x_3431_ = l_Lean_Fmt_fmt(v_dotTk_3430_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
v_a_3433_ = lean_ctor_get(v___x_3431_, 1);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3431_, 2);
v___x_3434_ = l_Lean_Fmt_fmt(v___x_3424_, v_a_3417_, v_a_3433_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3449_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_a_3436_ = lean_ctor_get(v___x_3434_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3438_ = v___x_3434_;
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3440_ = lean_unsigned_to_nat(2u);
v___x_3441_ = lean_mk_empty_array_with_capacity(v___x_3440_);
v___x_3442_ = lean_array_push(v___x_3441_, v_a_3432_);
v___x_3443_ = lean_array_push(v___x_3442_, v_a_3435_);
v___x_3444_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_3443_);
lean_dec_ref(v___x_3443_);
v___x_3445_ = l_Lean_Fmt_TaggedDoc_nested(v___x_3444_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3445_);
v___x_3447_ = v___x_3438_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_a_3436_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
else
{
lean_dec(v_a_3432_);
return v___x_3434_;
}
}
else
{
lean_dec(v___x_3424_);
return v___x_3431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDot___boxed(lean_object* v_x_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_Fmt_fmtGrindDot(v_x_3450_, v_a_3451_, v_a_3452_);
lean_dec_ref(v_a_3451_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1(){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3460_ = l_Lean_Fmt_fmtAttribute;
v___x_3461_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDot___closed__1));
v___x_3462_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___closed__1));
v___x_3463_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindDot___boxed), 3, 0);
v___x_3464_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3460_, v___x_3461_, v___x_3462_, v___x_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1___boxed(lean_object* v_a_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1();
return v_res_3466_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtGrindSeqFocus___closed__2(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = lean_box(0);
v___x_3474_ = lean_unsigned_to_nat(16u);
v___x_3475_ = lean_mk_array(v___x_3474_, v___x_3473_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtGrindSeqFocus___closed__3(void){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = lean_obj_once(&l_Lean_Fmt_fmtGrindSeqFocus___closed__2, &l_Lean_Fmt_fmtGrindSeqFocus___closed__2_once, _init_l_Lean_Fmt_fmtGrindSeqFocus___closed__2);
v___x_3477_ = lean_unsigned_to_nat(0u);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v___x_3476_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtGrindSeqFocus___closed__4(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; 
v___x_3479_ = lean_obj_once(&l_Lean_Fmt_fmtGrindSeqFocus___closed__3, &l_Lean_Fmt_fmtGrindSeqFocus___closed__3_once, _init_l_Lean_Fmt_fmtGrindSeqFocus___closed__3);
v___x_3480_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeqFocus___closed__1));
v___x_3481_ = 0;
v___x_3482_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set(v___x_3482_, 1, v___x_3479_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*2, v___x_3481_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*2 + 1, v___x_3481_);
return v___x_3482_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtGrindSeqFocus(void){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_obj_once(&l_Lean_Fmt_fmtGrindSeqFocus___closed__4, &l_Lean_Fmt_fmtGrindSeqFocus___closed__4_once, _init_l_Lean_Fmt_fmtGrindSeqFocus___closed__4);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1(){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3497_ = l_Lean_Fmt_infixFmtAttribute;
v___x_3498_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__1));
v___x_3499_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___closed__3));
v___x_3500_ = l_Lean_Fmt_fmtGrindSeqFocus;
v___x_3501_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3497_, v___x_3498_, v___x_3499_, v___x_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1___boxed(lean_object* v_a_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1();
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__1(size_t v_sz_3504_, size_t v_i_3505_, lean_object* v_bs_3506_){
_start:
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_usize_dec_lt(v_i_3505_, v_sz_3504_);
if (v___x_3507_ == 0)
{
return v_bs_3506_;
}
else
{
lean_object* v_v_3508_; lean_object* v_snd_3509_; lean_object* v_snd_3510_; lean_object* v___x_3511_; lean_object* v_bs_x27_3512_; size_t v___x_3513_; size_t v___x_3514_; lean_object* v___x_3515_; 
v_v_3508_ = lean_array_uget_borrowed(v_bs_3506_, v_i_3505_);
v_snd_3509_ = lean_ctor_get(v_v_3508_, 1);
v_snd_3510_ = lean_ctor_get(v_snd_3509_, 1);
lean_inc(v_snd_3510_);
v___x_3511_ = lean_unsigned_to_nat(0u);
v_bs_x27_3512_ = lean_array_uset(v_bs_3506_, v_i_3505_, v___x_3511_);
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3505_, v___x_3513_);
v___x_3515_ = lean_array_uset(v_bs_x27_3512_, v_i_3505_, v_snd_3510_);
v_i_3505_ = v___x_3514_;
v_bs_3506_ = v___x_3515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__1___boxed(lean_object* v_sz_3517_, lean_object* v_i_3518_, lean_object* v_bs_3519_){
_start:
{
size_t v_sz_boxed_3520_; size_t v_i_boxed_3521_; lean_object* v_res_3522_; 
v_sz_boxed_3520_ = lean_unbox_usize(v_sz_3517_);
lean_dec(v_sz_3517_);
v_i_boxed_3521_ = lean_unbox_usize(v_i_3518_);
lean_dec(v_i_3518_);
v_res_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__1(v_sz_boxed_3520_, v_i_boxed_3521_, v_bs_3519_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__2(size_t v_sz_3523_, size_t v_i_3524_, lean_object* v_bs_3525_){
_start:
{
uint8_t v___x_3526_; 
v___x_3526_ = lean_usize_dec_lt(v_i_3524_, v_sz_3523_);
if (v___x_3526_ == 0)
{
return v_bs_3525_;
}
else
{
lean_object* v_v_3527_; lean_object* v_snd_3528_; lean_object* v_fst_3529_; lean_object* v___x_3530_; lean_object* v_bs_x27_3531_; size_t v___x_3532_; size_t v___x_3533_; lean_object* v___x_3534_; 
v_v_3527_ = lean_array_uget_borrowed(v_bs_3525_, v_i_3524_);
v_snd_3528_ = lean_ctor_get(v_v_3527_, 1);
v_fst_3529_ = lean_ctor_get(v_snd_3528_, 0);
lean_inc(v_fst_3529_);
v___x_3530_ = lean_unsigned_to_nat(0u);
v_bs_x27_3531_ = lean_array_uset(v_bs_3525_, v_i_3524_, v___x_3530_);
v___x_3532_ = ((size_t)1ULL);
v___x_3533_ = lean_usize_add(v_i_3524_, v___x_3532_);
v___x_3534_ = lean_array_uset(v_bs_x27_3531_, v_i_3524_, v_fst_3529_);
v_i_3524_ = v___x_3533_;
v_bs_3525_ = v___x_3534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__2___boxed(lean_object* v_sz_3536_, lean_object* v_i_3537_, lean_object* v_bs_3538_){
_start:
{
size_t v_sz_boxed_3539_; size_t v_i_boxed_3540_; lean_object* v_res_3541_; 
v_sz_boxed_3539_ = lean_unbox_usize(v_sz_3536_);
lean_dec(v_sz_3536_);
v_i_boxed_3540_ = lean_unbox_usize(v_i_3537_);
lean_dec(v_i_3537_);
v_res_3541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__2(v_sz_boxed_3539_, v_i_boxed_3540_, v_bs_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0(size_t v_sz_3545_, size_t v_i_3546_, lean_object* v_bs_3547_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_usize_dec_lt(v_i_3546_, v_sz_3545_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_bs_3547_);
return v___x_3549_;
}
else
{
lean_object* v_v_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v_v_3550_ = lean_array_uget(v_bs_3547_, v_i_3546_);
v___x_3551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___closed__1));
lean_inc(v_v_3550_);
v___x_3552_ = l_Lean_Syntax_isOfKind(v_v_3550_, v___x_3551_);
if (v___x_3552_ == 0)
{
lean_object* v___x_3553_; 
lean_dec(v_v_3550_);
lean_dec_ref(v_bs_3547_);
v___x_3553_ = lean_box(0);
return v___x_3553_;
}
else
{
lean_object* v___x_3554_; lean_object* v_seqs_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v___x_3554_ = lean_unsigned_to_nat(1u);
v_seqs_3555_ = l_Lean_Syntax_getArg(v_v_3550_, v___x_3554_);
v___x_3556_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v_seqs_3555_);
v___x_3557_ = l_Lean_Syntax_isOfKind(v_seqs_3555_, v___x_3556_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; 
lean_dec(v_seqs_3555_);
lean_dec(v_v_3550_);
lean_dec_ref(v_bs_3547_);
v___x_3558_ = lean_box(0);
return v___x_3558_;
}
else
{
lean_object* v___x_3559_; lean_object* v_bs_x27_3560_; lean_object* v_lbTks_3561_; lean_object* v___x_3562_; lean_object* v_rbTks_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; size_t v___x_3566_; size_t v___x_3567_; lean_object* v___x_3568_; 
v___x_3559_ = lean_unsigned_to_nat(0u);
v_bs_x27_3560_ = lean_array_uset(v_bs_3547_, v_i_3546_, v___x_3559_);
v_lbTks_3561_ = l_Lean_Syntax_getArg(v_v_3550_, v___x_3559_);
v___x_3562_ = lean_unsigned_to_nat(2u);
v_rbTks_3563_ = l_Lean_Syntax_getArg(v_v_3550_, v___x_3562_);
lean_dec(v_v_3550_);
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v_seqs_3555_);
lean_ctor_set(v___x_3564_, 1, v_rbTks_3563_);
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v_lbTks_3561_);
lean_ctor_set(v___x_3565_, 1, v___x_3564_);
v___x_3566_ = ((size_t)1ULL);
v___x_3567_ = lean_usize_add(v_i_3546_, v___x_3566_);
v___x_3568_ = lean_array_uset(v_bs_x27_3560_, v_i_3546_, v___x_3565_);
v_i_3546_ = v___x_3567_;
v_bs_3547_ = v___x_3568_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0___boxed(lean_object* v_sz_3570_, lean_object* v_i_3571_, lean_object* v_bs_3572_){
_start:
{
size_t v_sz_boxed_3573_; size_t v_i_boxed_3574_; lean_object* v_res_3575_; 
v_sz_boxed_3573_ = lean_unbox_usize(v_sz_3570_);
lean_dec(v_sz_3570_);
v_i_boxed_3574_ = lean_unbox_usize(v_i_3571_);
lean_dec(v_i_3571_);
v_res_3575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0(v_sz_boxed_3573_, v_i_boxed_3574_, v_bs_3572_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__4(size_t v_sz_3576_, size_t v_i_3577_, lean_object* v_bs_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_usize_dec_lt(v_i_3577_, v_sz_3576_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; 
v___x_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3582_, 0, v_bs_3578_);
lean_ctor_set(v___x_3582_, 1, v___y_3580_);
return v___x_3582_;
}
else
{
lean_object* v_v_3583_; lean_object* v_snd_3584_; lean_object* v_fst_3585_; lean_object* v_fst_3586_; lean_object* v_snd_3587_; lean_object* v___x_3588_; 
v_v_3583_ = lean_array_uget_borrowed(v_bs_3578_, v_i_3577_);
v_snd_3584_ = lean_ctor_get(v_v_3583_, 1);
v_fst_3585_ = lean_ctor_get(v_v_3583_, 0);
v_fst_3586_ = lean_ctor_get(v_snd_3584_, 0);
v_snd_3587_ = lean_ctor_get(v_snd_3584_, 1);
lean_inc(v_fst_3585_);
v___x_3588_ = l_Lean_Fmt_fmt(v_fst_3585_, v___y_3579_, v___y_3580_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v_a_3590_; lean_object* v___x_3591_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
v_a_3590_ = lean_ctor_get(v___x_3588_, 1);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3588_, 2);
lean_inc(v_fst_3586_);
v___x_3591_ = l_Lean_Fmt_fmt(v_fst_3586_, v___y_3579_, v_a_3590_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v_a_3593_; lean_object* v___x_3594_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
v_a_3593_ = lean_ctor_get(v___x_3591_, 1);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3591_, 2);
lean_inc(v_snd_3587_);
v___x_3594_ = l_Lean_Fmt_fmt(v_snd_3587_, v___y_3579_, v_a_3593_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v_a_3596_; lean_object* v___x_3597_; lean_object* v_bs_x27_3598_; lean_object* v___x_3599_; size_t v___x_3600_; size_t v___x_3601_; lean_object* v___x_3602_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
v_a_3596_ = lean_ctor_get(v___x_3594_, 1);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3594_, 2);
v___x_3597_ = lean_unsigned_to_nat(0u);
v_bs_x27_3598_ = lean_array_uset(v_bs_3578_, v_i_3577_, v___x_3597_);
v___x_3599_ = l_Lean_Fmt_Layouts_parens(v_a_3589_, v_a_3592_, v_a_3595_);
v___x_3600_ = ((size_t)1ULL);
v___x_3601_ = lean_usize_add(v_i_3577_, v___x_3600_);
v___x_3602_ = lean_array_uset(v_bs_x27_3598_, v_i_3577_, v___x_3599_);
v_i_3577_ = v___x_3601_;
v_bs_3578_ = v___x_3602_;
v___y_3580_ = v_a_3596_;
goto _start;
}
else
{
lean_object* v_a_3604_; lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec(v_a_3592_);
lean_dec(v_a_3589_);
lean_dec_ref(v_bs_3578_);
v_a_3604_ = lean_ctor_get(v___x_3594_, 0);
v_a_3605_ = lean_ctor_get(v___x_3594_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3594_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_inc(v_a_3604_);
lean_dec(v___x_3594_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3604_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_a_3589_);
lean_dec_ref(v_bs_3578_);
v_a_3613_ = lean_ctor_get(v___x_3591_, 0);
v_a_3614_ = lean_ctor_get(v___x_3591_, 1);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3591_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_inc(v_a_3613_);
lean_dec(v___x_3591_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3613_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref(v_bs_3578_);
v_a_3622_ = lean_ctor_get(v___x_3588_, 0);
v_a_3623_ = lean_ctor_get(v___x_3588_, 1);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3588_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_inc(v_a_3622_);
lean_dec(v___x_3588_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3622_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__4___boxed(lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_bs_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
size_t v_sz_boxed_3636_; size_t v_i_boxed_3637_; lean_object* v_res_3638_; 
v_sz_boxed_3636_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3637_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__4(v_sz_boxed_3636_, v_i_boxed_3637_, v_bs_3633_, v___y_3634_, v___y_3635_);
lean_dec_ref(v___y_3634_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__3(size_t v_sz_3639_, size_t v_i_3640_, lean_object* v_bs_3641_){
_start:
{
uint8_t v___x_3642_; 
v___x_3642_ = lean_usize_dec_lt(v_i_3640_, v_sz_3639_);
if (v___x_3642_ == 0)
{
return v_bs_3641_;
}
else
{
lean_object* v_v_3643_; lean_object* v_fst_3644_; lean_object* v___x_3645_; lean_object* v_bs_x27_3646_; size_t v___x_3647_; size_t v___x_3648_; lean_object* v___x_3649_; 
v_v_3643_ = lean_array_uget_borrowed(v_bs_3641_, v_i_3640_);
v_fst_3644_ = lean_ctor_get(v_v_3643_, 0);
lean_inc(v_fst_3644_);
v___x_3645_ = lean_unsigned_to_nat(0u);
v_bs_x27_3646_ = lean_array_uset(v_bs_3641_, v_i_3640_, v___x_3645_);
v___x_3647_ = ((size_t)1ULL);
v___x_3648_ = lean_usize_add(v_i_3640_, v___x_3647_);
v___x_3649_ = lean_array_uset(v_bs_x27_3646_, v_i_3640_, v_fst_3644_);
v_i_3640_ = v___x_3648_;
v_bs_3641_ = v___x_3649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__3___boxed(lean_object* v_sz_3651_, lean_object* v_i_3652_, lean_object* v_bs_3653_){
_start:
{
size_t v_sz_boxed_3654_; size_t v_i_boxed_3655_; lean_object* v_res_3656_; 
v_sz_boxed_3654_ = lean_unbox_usize(v_sz_3651_);
lean_dec(v_sz_3651_);
v_i_boxed_3655_ = lean_unbox_usize(v_i_3652_);
lean_dec(v_i_3652_);
v_res_3656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__3(v_sz_boxed_3654_, v_i_boxed_3655_, v_bs_3653_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFirst(lean_object* v_x_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v___x_3667_; uint8_t v___x_3668_; 
v___x_3667_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFirst___closed__1));
lean_inc(v_x_3664_);
v___x_3668_ = l_Lean_Syntax_isOfKind(v_x_3664_, v___x_3667_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
lean_dec(v_x_3664_);
v___x_3669_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v_a_3666_);
return v___x_3670_;
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; size_t v_sz_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v___x_3671_ = lean_unsigned_to_nat(1u);
v___x_3672_ = l_Lean_Syntax_getArg(v_x_3664_, v___x_3671_);
v___x_3673_ = l_Lean_Syntax_getArgs(v___x_3672_);
lean_dec(v___x_3672_);
v_sz_3674_ = lean_array_size(v___x_3673_);
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__0(v_sz_3674_, v___x_3675_, v___x_3673_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_dec(v_x_3664_);
v___x_3677_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
lean_ctor_set(v___x_3678_, 1, v_a_3666_);
return v___x_3678_;
}
else
{
lean_object* v_val_3679_; lean_object* v___x_3680_; lean_object* v_firstTk_3681_; size_t v_sz_3682_; lean_object* v___x_3683_; 
v_val_3679_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_val_3679_);
lean_dec_ref_known(v___x_3676_, 1);
v___x_3680_ = lean_unsigned_to_nat(0u);
v_firstTk_3681_ = l_Lean_Syntax_getArg(v_x_3664_, v___x_3680_);
lean_dec(v_x_3664_);
v_sz_3682_ = lean_array_size(v_val_3679_);
v___x_3683_ = l_Lean_Fmt_fmt(v_firstTk_3681_, v_a_3665_, v_a_3666_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v_a_3685_; lean_object* v_rbTks_3686_; lean_object* v_seqs_3687_; lean_object* v_lbTks_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; size_t v_sz_3691_; lean_object* v___x_3692_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
v_a_3685_ = lean_ctor_get(v___x_3683_, 1);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3683_, 2);
lean_inc_n(v_val_3679_, 2);
v_rbTks_3686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__1(v_sz_3682_, v___x_3675_, v_val_3679_);
v_seqs_3687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__2(v_sz_3682_, v___x_3675_, v_val_3679_);
v_lbTks_3688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__3(v_sz_3682_, v___x_3675_, v_val_3679_);
v___x_3689_ = l_Array_zip___redArg(v_seqs_3687_, v_rbTks_3686_);
lean_dec_ref(v_rbTks_3686_);
lean_dec_ref(v_seqs_3687_);
v___x_3690_ = l_Array_zip___redArg(v_lbTks_3688_, v___x_3689_);
lean_dec_ref(v___x_3689_);
lean_dec_ref(v_lbTks_3688_);
v_sz_3691_ = lean_array_size(v___x_3690_);
v___x_3692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindFirst_spec__4(v_sz_3691_, v___x_3675_, v___x_3690_, v_a_3665_, v_a_3685_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3706_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
v_a_3694_ = lean_ctor_get(v___x_3692_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3696_ = v___x_3692_;
v_isShared_3697_ = v_isSharedCheck_3706_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_inc(v_a_3693_);
lean_dec(v___x_3692_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3706_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3698_ = lean_mk_empty_array_with_capacity(v___x_3671_);
v___x_3699_ = lean_array_push(v___x_3698_, v_a_3684_);
v___x_3700_ = l_Array_append___redArg(v___x_3699_, v_a_3693_);
lean_dec(v_a_3693_);
v___x_3701_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_3700_, v___x_3668_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = l_Lean_Fmt_TaggedDoc_nested(v___x_3701_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3702_);
v___x_3704_ = v___x_3696_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_a_3694_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec(v_a_3684_);
v_a_3707_ = lean_ctor_get(v___x_3692_, 0);
v_a_3708_ = lean_ctor_get(v___x_3692_, 1);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3692_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_inc(v_a_3707_);
lean_dec(v___x_3692_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3707_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_dec(v_val_3679_);
return v___x_3683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindFirst___boxed(lean_object* v_x_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_Fmt_fmtGrindFirst(v_x_3716_, v_a_3717_, v_a_3718_);
lean_dec_ref(v_a_3717_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1(){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3726_ = l_Lean_Fmt_fmtAttribute;
v___x_3727_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFirst___closed__1));
v___x_3728_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___closed__1));
v___x_3729_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindFirst___boxed), 3, 0);
v___x_3730_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3726_, v___x_3727_, v___x_3728_, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1___boxed(lean_object* v_a_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1();
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindParen(lean_object* v_x_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v___x_3743_; uint8_t v___x_3744_; 
v___x_3743_ = ((lean_object*)(l_Lean_Fmt_fmtGrindParen___closed__1));
lean_inc(v_x_3740_);
v___x_3744_ = l_Lean_Syntax_isOfKind(v_x_3740_, v___x_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v_x_3740_);
v___x_3745_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v_a_3742_);
return v___x_3746_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3747_ = lean_unsigned_to_nat(1u);
v___x_3748_ = l_Lean_Syntax_getArg(v_x_3740_, v___x_3747_);
v___x_3749_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3748_);
v___x_3750_ = l_Lean_Syntax_isOfKind(v___x_3748_, v___x_3749_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_dec(v___x_3748_);
lean_dec(v_x_3740_);
v___x_3751_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
lean_ctor_set(v___x_3752_, 1, v_a_3742_);
return v___x_3752_;
}
else
{
lean_object* v___x_3753_; lean_object* v_lbTk_3754_; lean_object* v___x_3755_; 
v___x_3753_ = lean_unsigned_to_nat(0u);
v_lbTk_3754_ = l_Lean_Syntax_getArg(v_x_3740_, v___x_3753_);
v___x_3755_ = l_Lean_Fmt_fmt(v_lbTk_3754_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v_a_3757_; lean_object* v___x_3758_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
v_a_3757_ = lean_ctor_get(v___x_3755_, 1);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3755_, 2);
v___x_3758_ = l_Lean_Fmt_fmt(v___x_3748_, v_a_3741_, v_a_3757_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v_a_3760_; lean_object* v___x_3761_; lean_object* v_rbTk_3762_; lean_object* v___x_3763_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
v_a_3760_ = lean_ctor_get(v___x_3758_, 1);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3758_, 2);
v___x_3761_ = lean_unsigned_to_nat(2u);
v_rbTk_3762_ = l_Lean_Syntax_getArg(v_x_3740_, v___x_3761_);
lean_dec(v_x_3740_);
v___x_3763_ = l_Lean_Fmt_fmt(v_rbTk_3762_, v_a_3741_, v_a_3760_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3773_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
v_a_3765_ = lean_ctor_get(v___x_3763_, 1);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3767_ = v___x_3763_;
v_isShared_3768_ = v_isSharedCheck_3773_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_inc(v_a_3764_);
lean_dec(v___x_3763_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3773_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3769_; lean_object* v___x_3771_; 
v___x_3769_ = l_Lean_Fmt_Layouts_parenthesizedSeq(v_a_3756_, v_a_3759_, v_a_3764_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v___x_3769_);
v___x_3771_ = v___x_3767_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_a_3765_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
else
{
lean_dec(v_a_3759_);
lean_dec(v_a_3756_);
return v___x_3763_;
}
}
else
{
lean_dec(v_a_3756_);
lean_dec(v_x_3740_);
return v___x_3758_;
}
}
else
{
lean_dec(v___x_3748_);
lean_dec(v_x_3740_);
return v___x_3755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindParen___boxed(lean_object* v_x_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_Fmt_fmtGrindParen(v_x_3774_, v_a_3775_, v_a_3776_);
lean_dec_ref(v_a_3775_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1(){
_start:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3784_ = l_Lean_Fmt_fmtAttribute;
v___x_3785_ = ((lean_object*)(l_Lean_Fmt_fmtGrindParen___closed__1));
v___x_3786_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___closed__1));
v___x_3787_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindParen___boxed), 3, 0);
v___x_3788_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3784_, v___x_3785_, v___x_3786_, v___x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1___boxed(lean_object* v_a_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1();
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSetOption(lean_object* v_x_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3803_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSetOption___closed__1));
lean_inc(v_x_3800_);
v___x_3804_ = l_Lean_Syntax_isOfKind(v_x_3800_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
lean_dec(v_x_3800_);
v___x_3805_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v_a_3802_);
return v___x_3806_;
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; 
v___x_3807_ = lean_unsigned_to_nat(1u);
v___x_3808_ = l_Lean_Syntax_getArg(v_x_3800_, v___x_3807_);
v___x_3809_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__3));
lean_inc(v___x_3808_);
v___x_3810_ = l_Lean_Syntax_isOfKind(v___x_3808_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_dec(v___x_3808_);
lean_dec(v_x_3800_);
v___x_3857_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
lean_ctor_set(v___x_3858_, 1, v_a_3802_);
return v___x_3858_;
}
else
{
lean_object* v___x_3859_; lean_object* v_setOptionTk_3860_; lean_object* v_dotTk_x3f_3862_; lean_object* v_idTail_x3f_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___x_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; 
v___x_3859_ = lean_unsigned_to_nat(0u);
v_setOptionTk_3860_ = l_Lean_Syntax_getArg(v_x_3800_, v___x_3859_);
v___x_3894_ = lean_unsigned_to_nat(2u);
v___x_3895_ = l_Lean_Syntax_getArg(v_x_3800_, v___x_3894_);
v___x_3896_ = l_Lean_Syntax_isNone(v___x_3895_);
if (v___x_3896_ == 0)
{
uint8_t v___x_3897_; 
lean_inc(v___x_3895_);
v___x_3897_ = l_Lean_Syntax_matchesNull(v___x_3895_, v___x_3894_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec(v___x_3895_);
lean_dec(v_setOptionTk_3860_);
lean_dec(v___x_3808_);
lean_dec(v_x_3800_);
v___x_3898_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
lean_ctor_set(v___x_3899_, 1, v_a_3802_);
return v___x_3899_;
}
else
{
lean_object* v_idTail_x3f_3900_; uint8_t v___x_3901_; 
v_idTail_x3f_3900_ = l_Lean_Syntax_getArg(v___x_3895_, v___x_3807_);
lean_inc(v_idTail_x3f_3900_);
v___x_3901_ = l_Lean_Syntax_isOfKind(v_idTail_x3f_3900_, v___x_3809_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec(v_idTail_x3f_3900_);
lean_dec(v___x_3895_);
lean_dec(v_setOptionTk_3860_);
lean_dec(v___x_3808_);
lean_dec(v_x_3800_);
v___x_3902_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v_a_3802_);
return v___x_3903_;
}
else
{
lean_object* v_dotTk_x3f_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_dotTk_x3f_3904_ = l_Lean_Syntax_getArg(v___x_3895_, v___x_3859_);
lean_dec(v___x_3895_);
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v_dotTk_x3f_3904_);
v___x_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3906_, 0, v_idTail_x3f_3900_);
v_dotTk_x3f_3862_ = v___x_3905_;
v_idTail_x3f_3863_ = v___x_3906_;
v___y_3864_ = v_a_3801_;
v___y_3865_ = v_a_3802_;
goto v___jp_3861_;
}
}
}
else
{
lean_object* v___x_3907_; 
lean_dec(v___x_3895_);
v___x_3907_ = lean_box(0);
v_dotTk_x3f_3862_ = v___x_3907_;
v_idTail_x3f_3863_ = v___x_3907_;
v___y_3864_ = v_a_3801_;
v___y_3865_ = v_a_3802_;
goto v___jp_3861_;
}
v___jp_3861_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3866_ = lean_unsigned_to_nat(5u);
v___x_3867_ = l_Lean_Syntax_getArg(v_x_3800_, v___x_3866_);
v___x_3868_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3867_);
v___x_3869_ = l_Lean_Syntax_isOfKind(v___x_3867_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_dec(v___x_3867_);
lean_dec(v_idTail_x3f_3863_);
lean_dec(v_dotTk_x3f_3862_);
lean_dec(v_setOptionTk_3860_);
lean_dec(v___x_3808_);
lean_dec(v_x_3800_);
v___x_3870_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
lean_ctor_set(v___x_3871_, 1, v___y_3865_);
return v___x_3871_;
}
else
{
lean_object* v___x_3872_; 
v___x_3872_ = l_Lean_Fmt_fmt(v_setOptionTk_3860_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v_a_3874_; lean_object* v___x_3875_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
v_a_3874_ = lean_ctor_get(v___x_3872_, 1);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3872_, 2);
v___x_3875_ = l_Lean_Fmt_fmt(v___x_3808_, v___y_3864_, v_a_3874_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v_a_3877_; lean_object* v___x_3878_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
v_a_3877_ = lean_ctor_get(v___x_3875_, 1);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3875_, 2);
v___x_3878_ = l_Lean_Fmt_fmt_x3f(v_dotTk_x3f_3862_, v___y_3864_, v_a_3877_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v_a_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v_inTk_3884_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
v_a_3880_ = lean_ctor_get(v___x_3878_, 1);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3878_, 2);
v___x_3881_ = lean_unsigned_to_nat(3u);
v___x_3882_ = l_Lean_Syntax_getArg(v_x_3800_, v___x_3881_);
v___x_3883_ = lean_unsigned_to_nat(4u);
v_inTk_3884_ = l_Lean_Syntax_getArg(v_x_3800_, v___x_3883_);
lean_dec(v_x_3800_);
if (lean_obj_tag(v_idTail_x3f_3863_) == 0)
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_box(0);
v___y_3812_ = v_a_3876_;
v___y_3813_ = v___x_3867_;
v___y_3814_ = v_a_3880_;
v___y_3815_ = v_inTk_3884_;
v___y_3816_ = v_a_3879_;
v___y_3817_ = v___x_3881_;
v___y_3818_ = v___y_3864_;
v___y_3819_ = v___x_3882_;
v___y_3820_ = v_a_3873_;
v___y_3821_ = v___x_3885_;
goto v___jp_3811_;
}
else
{
lean_object* v_val_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
v_val_3886_ = lean_ctor_get(v_idTail_x3f_3863_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_idTail_x3f_3863_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v_idTail_x3f_3863_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_val_3886_);
lean_dec(v_idTail_x3f_3863_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_val_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
v___y_3812_ = v_a_3876_;
v___y_3813_ = v___x_3867_;
v___y_3814_ = v_a_3880_;
v___y_3815_ = v_inTk_3884_;
v___y_3816_ = v_a_3879_;
v___y_3817_ = v___x_3881_;
v___y_3818_ = v___y_3864_;
v___y_3819_ = v___x_3882_;
v___y_3820_ = v_a_3873_;
v___y_3821_ = v___x_3891_;
goto v___jp_3811_;
}
}
}
}
else
{
lean_dec(v_a_3876_);
lean_dec(v_a_3873_);
lean_dec(v___x_3867_);
lean_dec(v_idTail_x3f_3863_);
lean_dec(v_x_3800_);
return v___x_3878_;
}
}
else
{
lean_dec(v_a_3873_);
lean_dec(v___x_3867_);
lean_dec(v_idTail_x3f_3863_);
lean_dec(v_dotTk_x3f_3862_);
lean_dec(v_x_3800_);
return v___x_3875_;
}
}
else
{
lean_dec(v___x_3867_);
lean_dec(v_idTail_x3f_3863_);
lean_dec(v_dotTk_x3f_3862_);
lean_dec(v___x_3808_);
lean_dec(v_x_3800_);
return v___x_3872_;
}
}
}
}
v___jp_3811_:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_Fmt_fmt_x3f(v___y_3821_, v___y_3818_, v___y_3814_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v_a_3824_; lean_object* v___x_3825_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
v_a_3824_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3822_, 2);
v___x_3825_ = l_Lean_Fmt_fmt(v___y_3819_, v___y_3818_, v_a_3824_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v_a_3827_; lean_object* v___x_3828_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
v_a_3827_ = lean_ctor_get(v___x_3825_, 1);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3825_, 2);
v___x_3828_ = l_Lean_Fmt_fmt(v___y_3815_, v___y_3818_, v_a_3827_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v_a_3830_; lean_object* v___x_3831_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
v_a_3830_ = lean_ctor_get(v___x_3828_, 1);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3828_, 2);
v___x_3831_ = l_Lean_Fmt_fmt(v___y_3813_, v___y_3818_, v_a_3830_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3856_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_a_3833_ = lean_ctor_get(v___x_3831_, 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3835_ = v___x_3831_;
v_isShared_3836_ = v_isSharedCheck_3856_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3856_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3837_ = lean_mk_empty_array_with_capacity(v___y_3817_);
lean_inc_ref(v___x_3837_);
v___x_3838_ = lean_array_push(v___x_3837_, v___y_3812_);
v___x_3839_ = lean_array_push(v___x_3838_, v___y_3816_);
v___x_3840_ = lean_array_push(v___x_3839_, v_a_3823_);
v___x_3841_ = l_Lean_Fmt_Layouts_atomic(v___x_3840_);
lean_dec_ref(v___x_3840_);
v___x_3842_ = lean_array_push(v___x_3837_, v___y_3820_);
v___x_3843_ = lean_array_push(v___x_3842_, v___x_3841_);
v___x_3844_ = lean_array_push(v___x_3843_, v_a_3826_);
v___x_3845_ = 0;
v___x_3846_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3846_, 0, v___x_3810_);
lean_ctor_set_uint8(v___x_3846_, 1, v___x_3845_);
lean_ctor_set_uint8(v___x_3846_, 2, v___x_3845_);
lean_ctor_set_uint8(v___x_3846_, 3, v___x_3845_);
v___x_3847_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3844_, v___x_3846_);
v___x_3848_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3848_, 0, v___x_3845_);
lean_ctor_set_uint8(v___x_3848_, 1, v___x_3810_);
lean_inc(v_a_3832_);
lean_inc(v_a_3829_);
lean_inc_ref(v___x_3847_);
v___x_3849_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3847_, v_a_3829_, v_a_3832_, v___x_3848_);
v___x_3850_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSetOption___closed__2));
v___x_3851_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3847_, v_a_3829_, v_a_3832_, v___x_3850_);
v___x_3852_ = l_Lean_Fmt_TaggedDoc_pseudoDedented(v___x_3849_, v___x_3851_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3852_);
v___x_3854_ = v___x_3835_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_a_3833_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
else
{
lean_dec(v_a_3829_);
lean_dec(v_a_3826_);
lean_dec(v_a_3823_);
lean_dec_ref(v___y_3820_);
lean_dec_ref(v___y_3816_);
lean_dec_ref(v___y_3812_);
return v___x_3831_;
}
}
else
{
lean_dec(v_a_3826_);
lean_dec(v_a_3823_);
lean_dec_ref(v___y_3820_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
return v___x_3828_;
}
}
else
{
lean_dec(v_a_3823_);
lean_dec_ref(v___y_3820_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
return v___x_3825_;
}
}
else
{
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
return v___x_3822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSetOption___boxed(lean_object* v_x_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Fmt_fmtGrindSetOption(v_x_3908_, v_a_3909_, v_a_3910_);
lean_dec_ref(v_a_3909_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1(){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3918_ = l_Lean_Fmt_fmtAttribute;
v___x_3919_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSetOption___closed__1));
v___x_3920_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___closed__1));
v___x_3921_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSetOption___boxed), 3, 0);
v___x_3922_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3918_, v___x_3919_, v___x_3920_, v___x_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1___boxed(lean_object* v_a_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1();
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSetConfig(lean_object* v_x_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3935_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSetConfig___closed__1));
lean_inc(v_x_3932_);
v___x_3936_ = l_Lean_Syntax_isOfKind(v_x_3932_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
lean_dec(v_x_3932_);
v___x_3937_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
lean_ctor_set(v___x_3938_, 1, v_a_3934_);
return v___x_3938_;
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; uint8_t v___x_3942_; 
v___x_3939_ = lean_unsigned_to_nat(3u);
v___x_3940_ = l_Lean_Syntax_getArg(v_x_3932_, v___x_3939_);
v___x_3941_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSeq___closed__1));
lean_inc(v___x_3940_);
v___x_3942_ = l_Lean_Syntax_isOfKind(v___x_3940_, v___x_3941_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec(v___x_3940_);
lean_dec(v_x_3932_);
v___x_3943_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
lean_ctor_set(v___x_3944_, 1, v_a_3934_);
return v___x_3944_;
}
else
{
lean_object* v___x_3945_; lean_object* v_setConfigTk_3946_; lean_object* v___x_3947_; 
v___x_3945_ = lean_unsigned_to_nat(0u);
v_setConfigTk_3946_ = l_Lean_Syntax_getArg(v_x_3932_, v___x_3945_);
v___x_3947_ = l_Lean_Fmt_fmt(v_setConfigTk_3946_, v_a_3933_, v_a_3934_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v_a_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v_cfgItems_3952_; lean_object* v___x_3953_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
v_a_3949_ = lean_ctor_get(v___x_3947_, 1);
lean_inc(v_a_3949_);
lean_dec_ref_known(v___x_3947_, 2);
v___x_3950_ = lean_unsigned_to_nat(1u);
v___x_3951_ = l_Lean_Syntax_getArg(v_x_3932_, v___x_3950_);
v_cfgItems_3952_ = l_Lean_Syntax_getArgs(v___x_3951_);
lean_dec(v___x_3951_);
v___x_3953_ = l_Lean_Fmt_fmtArray___redArg(v_cfgItems_3952_, v_a_3933_, v_a_3949_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v_a_3955_; lean_object* v___x_3956_; lean_object* v_inTk_3957_; uint8_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
v_a_3955_ = lean_ctor_get(v___x_3953_, 1);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3953_, 2);
v___x_3956_ = lean_unsigned_to_nat(2u);
v_inTk_3957_ = l_Lean_Syntax_getArg(v_x_3932_, v___x_3956_);
lean_dec(v_x_3932_);
v___x_3958_ = 0;
v___x_3959_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3959_, 0, v___x_3942_);
lean_ctor_set_uint8(v___x_3959_, 1, v___x_3958_);
lean_ctor_set_uint8(v___x_3959_, 2, v___x_3958_);
lean_ctor_set_uint8(v___x_3959_, 3, v___x_3958_);
v___x_3960_ = l_Lean_Fmt_fmt(v_inTk_3957_, v_a_3933_, v_a_3955_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v_a_3962_; lean_object* v___x_3963_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
v_a_3962_ = lean_ctor_get(v___x_3960_, 1);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3960_, 2);
v___x_3963_ = l_Lean_Fmt_fmt(v___x_3940_, v_a_3933_, v_a_3962_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3981_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_a_3965_ = lean_ctor_get(v___x_3963_, 1);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3967_ = v___x_3963_;
v_isShared_3968_ = v_isSharedCheck_3981_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3981_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3969_ = lean_mk_empty_array_with_capacity(v___x_3950_);
v___x_3970_ = lean_array_push(v___x_3969_, v_a_3948_);
v___x_3971_ = l_Array_append___redArg(v___x_3970_, v_a_3954_);
lean_dec(v_a_3954_);
v___x_3972_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3971_, v___x_3959_);
v___x_3973_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3973_, 0, v___x_3958_);
lean_ctor_set_uint8(v___x_3973_, 1, v___x_3942_);
lean_inc(v_a_3964_);
lean_inc(v_a_3961_);
lean_inc_ref(v___x_3972_);
v___x_3974_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3972_, v_a_3961_, v_a_3964_, v___x_3973_);
v___x_3975_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSetOption___closed__2));
v___x_3976_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3972_, v_a_3961_, v_a_3964_, v___x_3975_);
v___x_3977_ = l_Lean_Fmt_TaggedDoc_pseudoDedented(v___x_3974_, v___x_3976_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_3977_);
v___x_3979_ = v___x_3967_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_a_3965_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
else
{
lean_dec(v_a_3961_);
lean_dec_ref_known(v___x_3959_, 0);
lean_dec(v_a_3954_);
lean_dec(v_a_3948_);
return v___x_3963_;
}
}
else
{
lean_dec_ref_known(v___x_3959_, 0);
lean_dec(v_a_3954_);
lean_dec(v_a_3948_);
lean_dec(v___x_3940_);
return v___x_3960_;
}
}
else
{
lean_object* v_a_3982_; lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
lean_dec(v_a_3948_);
lean_dec(v___x_3940_);
lean_dec(v_x_3932_);
v_a_3982_ = lean_ctor_get(v___x_3953_, 0);
v_a_3983_ = lean_ctor_get(v___x_3953_, 1);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3953_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_inc(v_a_3982_);
lean_dec(v___x_3953_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3982_);
lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_a_3983_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
else
{
lean_dec(v___x_3940_);
lean_dec(v_x_3932_);
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSetConfig___boxed(lean_object* v_x_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Fmt_fmtGrindSetConfig(v_x_3991_, v_a_3992_, v_a_3993_);
lean_dec_ref(v_a_3992_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1(){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4001_ = l_Lean_Fmt_fmtAttribute;
v___x_4002_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSetConfig___closed__1));
v___x_4003_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___closed__1));
v___x_4004_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSetConfig___boxed), 3, 0);
v___x_4005_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4001_, v___x_4002_, v___x_4003_, v___x_4004_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1___boxed(lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1();
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntro(lean_object* v_x_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v___x_4018_; uint8_t v___x_4019_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; 
v___x_4018_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSymIntro___closed__1));
lean_inc(v_x_4015_);
v___x_4019_ = l_Lean_Syntax_isOfKind(v_x_4015_, v___x_4018_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_dec(v_x_4015_);
v___x_4064_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set(v___x_4065_, 1, v_a_4017_);
return v___x_4065_;
}
else
{
lean_object* v___x_4066_; lean_object* v_introTk_4067_; lean_object* v_lbTk_x3f_4069_; lean_object* v_intTk_x3f_4070_; lean_object* v_ceqTk_x3f_4071_; lean_object* v_bVal_x3f_4072_; lean_object* v_rbTk_x3f_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v___x_4066_ = lean_unsigned_to_nat(0u);
v_introTk_4067_ = l_Lean_Syntax_getArg(v_x_4015_, v___x_4066_);
v___x_4092_ = lean_unsigned_to_nat(1u);
v___x_4093_ = l_Lean_Syntax_getArg(v_x_4015_, v___x_4092_);
v___x_4094_ = l_Lean_Syntax_isNone(v___x_4093_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; uint8_t v___x_4096_; 
v___x_4095_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_4093_);
v___x_4096_ = l_Lean_Syntax_matchesNull(v___x_4093_, v___x_4095_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_dec(v___x_4093_);
lean_dec(v_introTk_4067_);
lean_dec(v_x_4015_);
v___x_4097_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v_a_4017_);
return v___x_4098_;
}
else
{
lean_object* v_lbTk_x3f_4099_; lean_object* v_intTk_x3f_4100_; lean_object* v___x_4101_; lean_object* v_ceqTk_x3f_4102_; lean_object* v___x_4103_; lean_object* v_bVal_x3f_4104_; lean_object* v___x_4105_; lean_object* v_rbTk_x3f_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_lbTk_x3f_4099_ = l_Lean_Syntax_getArg(v___x_4093_, v___x_4066_);
v_intTk_x3f_4100_ = l_Lean_Syntax_getArg(v___x_4093_, v___x_4092_);
v___x_4101_ = lean_unsigned_to_nat(2u);
v_ceqTk_x3f_4102_ = l_Lean_Syntax_getArg(v___x_4093_, v___x_4101_);
v___x_4103_ = lean_unsigned_to_nat(3u);
v_bVal_x3f_4104_ = l_Lean_Syntax_getArg(v___x_4093_, v___x_4103_);
v___x_4105_ = lean_unsigned_to_nat(4u);
v_rbTk_x3f_4106_ = l_Lean_Syntax_getArg(v___x_4093_, v___x_4105_);
lean_dec(v___x_4093_);
v___x_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_lbTk_x3f_4099_);
v___x_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_intTk_x3f_4100_);
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_ceqTk_x3f_4102_);
v___x_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4110_, 0, v_bVal_x3f_4104_);
v___x_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4111_, 0, v_rbTk_x3f_4106_);
v_lbTk_x3f_4069_ = v___x_4107_;
v_intTk_x3f_4070_ = v___x_4108_;
v_ceqTk_x3f_4071_ = v___x_4109_;
v_bVal_x3f_4072_ = v___x_4110_;
v_rbTk_x3f_4073_ = v___x_4111_;
v___y_4074_ = v_a_4016_;
v___y_4075_ = v_a_4017_;
goto v___jp_4068_;
}
}
else
{
lean_object* v___x_4112_; 
lean_dec(v___x_4093_);
v___x_4112_ = lean_box(0);
v_lbTk_x3f_4069_ = v___x_4112_;
v_intTk_x3f_4070_ = v___x_4112_;
v_ceqTk_x3f_4071_ = v___x_4112_;
v_bVal_x3f_4072_ = v___x_4112_;
v_rbTk_x3f_4073_ = v___x_4112_;
v___y_4074_ = v_a_4016_;
v___y_4075_ = v_a_4017_;
goto v___jp_4068_;
}
v___jp_4068_:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_Fmt_fmt(v_introTk_4067_, v___y_4074_, v___y_4075_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v_a_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v_ids_4081_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
v_a_4078_ = lean_ctor_get(v___x_4076_, 1);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4076_, 2);
v___x_4079_ = lean_unsigned_to_nat(2u);
v___x_4080_ = l_Lean_Syntax_getArg(v_x_4015_, v___x_4079_);
lean_dec(v_x_4015_);
v_ids_4081_ = l_Lean_Syntax_getArgs(v___x_4080_);
lean_dec(v___x_4080_);
if (lean_obj_tag(v_bVal_x3f_4072_) == 0)
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_box(0);
v___y_4021_ = v_a_4077_;
v___y_4022_ = v_a_4078_;
v___y_4023_ = v___x_4079_;
v___y_4024_ = v_rbTk_x3f_4073_;
v___y_4025_ = v___y_4074_;
v___y_4026_ = v_intTk_x3f_4070_;
v___y_4027_ = v_ceqTk_x3f_4071_;
v___y_4028_ = v_ids_4081_;
v___y_4029_ = v_lbTk_x3f_4069_;
v___y_4030_ = v___x_4082_;
goto v___jp_4020_;
}
else
{
lean_object* v_val_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4091_; 
v_val_4083_ = lean_ctor_get(v_bVal_x3f_4072_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v_bVal_x3f_4072_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4085_ = v_bVal_x3f_4072_;
v_isShared_4086_ = v_isSharedCheck_4091_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_val_4083_);
lean_dec(v_bVal_x3f_4072_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4091_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4087_; lean_object* v___x_4089_; 
v___x_4087_ = l_Lean_Syntax_getArg(v_val_4083_, v___x_4066_);
lean_dec(v_val_4083_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4087_);
v___x_4089_ = v___x_4085_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
v___y_4021_ = v_a_4077_;
v___y_4022_ = v_a_4078_;
v___y_4023_ = v___x_4079_;
v___y_4024_ = v_rbTk_x3f_4073_;
v___y_4025_ = v___y_4074_;
v___y_4026_ = v_intTk_x3f_4070_;
v___y_4027_ = v_ceqTk_x3f_4071_;
v___y_4028_ = v_ids_4081_;
v___y_4029_ = v_lbTk_x3f_4069_;
v___y_4030_ = v___x_4089_;
goto v___jp_4020_;
}
}
}
}
else
{
lean_dec(v_rbTk_x3f_4073_);
lean_dec(v_bVal_x3f_4072_);
lean_dec(v_ceqTk_x3f_4071_);
lean_dec(v_intTk_x3f_4070_);
lean_dec(v_lbTk_x3f_4069_);
lean_dec(v_x_4015_);
return v___x_4076_;
}
}
}
v___jp_4020_:
{
lean_object* v___x_4031_; 
v___x_4031_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_4029_, v___y_4026_, v___y_4027_, v___y_4030_, v___y_4024_, v___y_4025_, v___y_4022_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v_a_4033_; uint8_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
v_a_4033_ = lean_ctor_get(v___x_4031_, 1);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4031_, 2);
v___x_4034_ = 0;
v___x_4035_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4035_, 0, v___x_4019_);
lean_ctor_set_uint8(v___x_4035_, 1, v___x_4034_);
lean_ctor_set_uint8(v___x_4035_, 2, v___x_4034_);
lean_ctor_set_uint8(v___x_4035_, 3, v___x_4034_);
v___x_4036_ = l_Lean_Fmt_fmtArray___redArg(v___y_4028_, v___y_4025_, v_a_4033_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4054_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_a_4038_ = lean_ctor_get(v___x_4036_, 1);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4040_ = v___x_4036_;
v_isShared_4041_ = v_isSharedCheck_4054_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4054_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
v___x_4042_ = lean_mk_empty_array_with_capacity(v___y_4023_);
v___x_4043_ = lean_array_push(v___x_4042_, v___y_4021_);
v___x_4044_ = lean_array_push(v___x_4043_, v_a_4032_);
lean_inc_ref(v___x_4035_);
v___x_4045_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4044_, v___x_4035_);
v___x_4046_ = lean_unsigned_to_nat(1u);
v___x_4047_ = lean_mk_empty_array_with_capacity(v___x_4046_);
v___x_4048_ = lean_array_push(v___x_4047_, v___x_4045_);
v___x_4049_ = l_Array_append___redArg(v___x_4048_, v_a_4037_);
lean_dec(v_a_4037_);
v___x_4050_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4049_, v___x_4035_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4050_);
v___x_4052_ = v___x_4040_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_a_4038_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec_ref_known(v___x_4035_, 0);
lean_dec(v_a_4032_);
lean_dec_ref(v___y_4021_);
v_a_4055_ = lean_ctor_get(v___x_4036_, 0);
v_a_4056_ = lean_ctor_get(v___x_4036_, 1);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4036_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_inc(v_a_4055_);
lean_dec(v___x_4036_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4055_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
else
{
lean_dec_ref(v___y_4028_);
lean_dec_ref(v___y_4021_);
return v___x_4031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntro___boxed(lean_object* v_x_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Fmt_fmtGrindSymIntro(v_x_4113_, v_a_4114_, v_a_4115_);
lean_dec_ref(v_a_4114_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1(){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4123_ = l_Lean_Fmt_fmtAttribute;
v___x_4124_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSymIntro___closed__1));
v___x_4125_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___closed__1));
v___x_4126_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSymIntro___boxed), 3, 0);
v___x_4127_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4123_, v___x_4124_, v___x_4125_, v___x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1___boxed(lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1();
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntroLight(lean_object* v_x_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4140_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSymIntroLight___closed__1));
lean_inc(v_x_4137_);
v___x_4141_ = l_Lean_Syntax_isOfKind(v_x_4137_, v___x_4140_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_dec(v_x_4137_);
v___x_4142_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
lean_ctor_set(v___x_4143_, 1, v_a_4139_);
return v___x_4143_;
}
else
{
lean_object* v___x_4144_; lean_object* v_introTk_4145_; lean_object* v___x_4146_; 
v___x_4144_ = lean_unsigned_to_nat(0u);
v_introTk_4145_ = l_Lean_Syntax_getArg(v_x_4137_, v___x_4144_);
v___x_4146_ = l_Lean_Fmt_fmt(v_introTk_4145_, v_a_4138_, v_a_4139_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v_a_4148_; lean_object* v___x_4149_; lean_object* v_tildeTk_4150_; lean_object* v___x_4151_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
v_a_4148_ = lean_ctor_get(v___x_4146_, 1);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4146_, 2);
v___x_4149_ = lean_unsigned_to_nat(1u);
v_tildeTk_4150_ = l_Lean_Syntax_getArg(v_x_4137_, v___x_4149_);
v___x_4151_ = l_Lean_Fmt_fmt(v_tildeTk_4150_, v_a_4138_, v_a_4148_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v_a_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v_ids_4156_; lean_object* v___x_4157_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
v_a_4153_ = lean_ctor_get(v___x_4151_, 1);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4151_, 2);
v___x_4154_ = lean_unsigned_to_nat(2u);
v___x_4155_ = l_Lean_Syntax_getArg(v_x_4137_, v___x_4154_);
lean_dec(v_x_4137_);
v_ids_4156_ = l_Lean_Syntax_getArgs(v___x_4155_);
lean_dec(v___x_4155_);
v___x_4157_ = l_Lean_Fmt_fmtArray___redArg(v_ids_4156_, v_a_4138_, v_a_4153_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4176_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_a_4159_ = lean_ctor_get(v___x_4157_, 1);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4161_ = v___x_4157_;
v_isShared_4162_ = v_isSharedCheck_4176_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4176_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
v___x_4163_ = lean_mk_empty_array_with_capacity(v___x_4154_);
v___x_4164_ = lean_array_push(v___x_4163_, v_a_4147_);
v___x_4165_ = lean_array_push(v___x_4164_, v_a_4152_);
v___x_4166_ = l_Lean_Fmt_Layouts_atomic(v___x_4165_);
lean_dec_ref(v___x_4165_);
v___x_4167_ = lean_mk_empty_array_with_capacity(v___x_4149_);
v___x_4168_ = lean_array_push(v___x_4167_, v___x_4166_);
v___x_4169_ = l_Array_append___redArg(v___x_4168_, v_a_4158_);
lean_dec(v_a_4158_);
v___x_4170_ = 0;
v___x_4171_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4171_, 0, v___x_4141_);
lean_ctor_set_uint8(v___x_4171_, 1, v___x_4170_);
lean_ctor_set_uint8(v___x_4171_, 2, v___x_4170_);
lean_ctor_set_uint8(v___x_4171_, 3, v___x_4170_);
v___x_4172_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4169_, v___x_4171_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4172_);
v___x_4174_ = v___x_4161_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v_a_4159_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_dec(v_a_4152_);
lean_dec(v_a_4147_);
v_a_4177_ = lean_ctor_get(v___x_4157_, 0);
v_a_4178_ = lean_ctor_get(v___x_4157_, 1);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4157_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_inc(v_a_4177_);
lean_dec(v___x_4157_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4177_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
else
{
lean_dec(v_a_4147_);
lean_dec(v_x_4137_);
return v___x_4151_;
}
}
else
{
lean_dec(v_x_4137_);
return v___x_4146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntroLight___boxed(lean_object* v_x_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_Fmt_fmtGrindSymIntroLight(v_x_4186_, v_a_4187_, v_a_4188_);
lean_dec_ref(v_a_4187_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1(){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4196_ = l_Lean_Fmt_fmtAttribute;
v___x_4197_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSymIntroLight___closed__1));
v___x_4198_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___closed__1));
v___x_4199_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSymIntroLight___boxed), 3, 0);
v___x_4200_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4196_, v___x_4197_, v___x_4198_, v___x_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1___boxed(lean_object* v_a_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1();
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntros(lean_object* v_x_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___x_4213_; uint8_t v___x_4214_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; 
v___x_4213_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSymIntros___closed__1));
lean_inc(v_x_4210_);
v___x_4214_ = l_Lean_Syntax_isOfKind(v_x_4210_, v___x_4213_);
if (v___x_4214_ == 0)
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_dec(v_x_4210_);
v___x_4241_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
lean_ctor_set(v___x_4242_, 1, v_a_4212_);
return v___x_4242_;
}
else
{
lean_object* v___x_4243_; lean_object* v_introsTk_4244_; lean_object* v_lbTk_x3f_4246_; lean_object* v_intTk_x3f_4247_; lean_object* v_ceqTk_x3f_4248_; lean_object* v_bVal_x3f_4249_; lean_object* v_rbTk_x3f_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v___x_4243_ = lean_unsigned_to_nat(0u);
v_introsTk_4244_ = l_Lean_Syntax_getArg(v_x_4210_, v___x_4243_);
v___x_4268_ = lean_unsigned_to_nat(1u);
v___x_4269_ = l_Lean_Syntax_getArg(v_x_4210_, v___x_4268_);
lean_dec(v_x_4210_);
v___x_4270_ = l_Lean_Syntax_isNone(v___x_4269_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; uint8_t v___x_4272_; 
v___x_4271_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_4269_);
v___x_4272_ = l_Lean_Syntax_matchesNull(v___x_4269_, v___x_4271_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_dec(v___x_4269_);
lean_dec(v_introsTk_4244_);
v___x_4273_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
lean_ctor_set(v___x_4274_, 1, v_a_4212_);
return v___x_4274_;
}
else
{
lean_object* v_lbTk_x3f_4275_; lean_object* v_intTk_x3f_4276_; lean_object* v___x_4277_; lean_object* v_ceqTk_x3f_4278_; lean_object* v___x_4279_; lean_object* v_bVal_x3f_4280_; lean_object* v___x_4281_; lean_object* v_rbTk_x3f_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_lbTk_x3f_4275_ = l_Lean_Syntax_getArg(v___x_4269_, v___x_4243_);
v_intTk_x3f_4276_ = l_Lean_Syntax_getArg(v___x_4269_, v___x_4268_);
v___x_4277_ = lean_unsigned_to_nat(2u);
v_ceqTk_x3f_4278_ = l_Lean_Syntax_getArg(v___x_4269_, v___x_4277_);
v___x_4279_ = lean_unsigned_to_nat(3u);
v_bVal_x3f_4280_ = l_Lean_Syntax_getArg(v___x_4269_, v___x_4279_);
v___x_4281_ = lean_unsigned_to_nat(4u);
v_rbTk_x3f_4282_ = l_Lean_Syntax_getArg(v___x_4269_, v___x_4281_);
lean_dec(v___x_4269_);
v___x_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4283_, 0, v_lbTk_x3f_4275_);
v___x_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4284_, 0, v_intTk_x3f_4276_);
v___x_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4285_, 0, v_ceqTk_x3f_4278_);
v___x_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4286_, 0, v_bVal_x3f_4280_);
v___x_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4287_, 0, v_rbTk_x3f_4282_);
v_lbTk_x3f_4246_ = v___x_4283_;
v_intTk_x3f_4247_ = v___x_4284_;
v_ceqTk_x3f_4248_ = v___x_4285_;
v_bVal_x3f_4249_ = v___x_4286_;
v_rbTk_x3f_4250_ = v___x_4287_;
v___y_4251_ = v_a_4211_;
v___y_4252_ = v_a_4212_;
goto v___jp_4245_;
}
}
else
{
lean_object* v___x_4288_; 
lean_dec(v___x_4269_);
v___x_4288_ = lean_box(0);
v_lbTk_x3f_4246_ = v___x_4288_;
v_intTk_x3f_4247_ = v___x_4288_;
v_ceqTk_x3f_4248_ = v___x_4288_;
v_bVal_x3f_4249_ = v___x_4288_;
v_rbTk_x3f_4250_ = v___x_4288_;
v___y_4251_ = v_a_4211_;
v___y_4252_ = v_a_4212_;
goto v___jp_4245_;
}
v___jp_4245_:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Fmt_fmt(v_introsTk_4244_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4253_) == 0)
{
if (lean_obj_tag(v_bVal_x3f_4249_) == 0)
{
lean_object* v_a_4254_; lean_object* v_a_4255_; lean_object* v___x_4256_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
v_a_4255_ = lean_ctor_get(v___x_4253_, 1);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4253_, 2);
v___x_4256_ = lean_box(0);
v___y_4216_ = v_a_4255_;
v___y_4217_ = v_a_4254_;
v___y_4218_ = v_rbTk_x3f_4250_;
v___y_4219_ = v___y_4251_;
v___y_4220_ = v_lbTk_x3f_4246_;
v___y_4221_ = v_intTk_x3f_4247_;
v___y_4222_ = v_ceqTk_x3f_4248_;
v___y_4223_ = v___x_4256_;
goto v___jp_4215_;
}
else
{
lean_object* v_a_4257_; lean_object* v_a_4258_; lean_object* v_val_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4267_; 
v_a_4257_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4257_);
v_a_4258_ = lean_ctor_get(v___x_4253_, 1);
lean_inc(v_a_4258_);
lean_dec_ref_known(v___x_4253_, 2);
v_val_4259_ = lean_ctor_get(v_bVal_x3f_4249_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_bVal_x3f_4249_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4261_ = v_bVal_x3f_4249_;
v_isShared_4262_ = v_isSharedCheck_4267_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_val_4259_);
lean_dec(v_bVal_x3f_4249_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4267_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4263_; lean_object* v___x_4265_; 
v___x_4263_ = l_Lean_Syntax_getArg(v_val_4259_, v___x_4243_);
lean_dec(v_val_4259_);
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 0, v___x_4263_);
v___x_4265_ = v___x_4261_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
v___y_4216_ = v_a_4258_;
v___y_4217_ = v_a_4257_;
v___y_4218_ = v_rbTk_x3f_4250_;
v___y_4219_ = v___y_4251_;
v___y_4220_ = v_lbTk_x3f_4246_;
v___y_4221_ = v_intTk_x3f_4247_;
v___y_4222_ = v_ceqTk_x3f_4248_;
v___y_4223_ = v___x_4265_;
goto v___jp_4215_;
}
}
}
}
else
{
lean_dec(v_rbTk_x3f_4250_);
lean_dec(v_bVal_x3f_4249_);
lean_dec(v_ceqTk_x3f_4248_);
lean_dec(v_intTk_x3f_4247_);
lean_dec(v_lbTk_x3f_4246_);
return v___x_4253_;
}
}
}
v___jp_4215_:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4218_, v___y_4219_, v___y_4216_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4240_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_a_4226_ = lean_ctor_get(v___x_4224_, 1);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4228_ = v___x_4224_;
v_isShared_4229_ = v_isSharedCheck_4240_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4240_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4238_; 
v___x_4230_ = lean_unsigned_to_nat(2u);
v___x_4231_ = lean_mk_empty_array_with_capacity(v___x_4230_);
v___x_4232_ = lean_array_push(v___x_4231_, v___y_4217_);
v___x_4233_ = lean_array_push(v___x_4232_, v_a_4225_);
v___x_4234_ = 0;
v___x_4235_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4235_, 0, v___x_4214_);
lean_ctor_set_uint8(v___x_4235_, 1, v___x_4234_);
lean_ctor_set_uint8(v___x_4235_, 2, v___x_4234_);
lean_ctor_set_uint8(v___x_4235_, 3, v___x_4234_);
v___x_4236_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4233_, v___x_4235_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4236_);
v___x_4238_ = v___x_4228_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4236_);
lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_a_4226_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
else
{
lean_dec_ref(v___y_4217_);
return v___x_4224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntros___boxed(lean_object* v_x_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Fmt_fmtGrindSymIntros(v_x_4289_, v_a_4290_, v_a_4291_);
lean_dec_ref(v_a_4290_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1(){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4299_ = l_Lean_Fmt_fmtAttribute;
v___x_4300_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSymIntros___closed__1));
v___x_4301_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___closed__1));
v___x_4302_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSymIntros___boxed), 3, 0);
v___x_4303_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4299_, v___x_4300_, v___x_4301_, v___x_4302_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1___boxed(lean_object* v_a_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1();
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntrosLight(lean_object* v_x_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4316_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1));
lean_inc(v_x_4313_);
v___x_4317_ = l_Lean_Syntax_isOfKind(v_x_4313_, v___x_4316_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
lean_dec(v_x_4313_);
v___x_4318_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
lean_ctor_set(v___x_4319_, 1, v_a_4315_);
return v___x_4319_;
}
else
{
lean_object* v___x_4320_; lean_object* v_introsTk_4321_; lean_object* v___x_4322_; 
v___x_4320_ = lean_unsigned_to_nat(0u);
v_introsTk_4321_ = l_Lean_Syntax_getArg(v_x_4313_, v___x_4320_);
v___x_4322_ = l_Lean_Fmt_fmt(v_introsTk_4321_, v_a_4314_, v_a_4315_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v_a_4324_; lean_object* v___x_4325_; lean_object* v_tildeTk_4326_; lean_object* v___x_4327_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
v_a_4324_ = lean_ctor_get(v___x_4322_, 1);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4322_, 2);
v___x_4325_ = lean_unsigned_to_nat(1u);
v_tildeTk_4326_ = l_Lean_Syntax_getArg(v_x_4313_, v___x_4325_);
lean_dec(v_x_4313_);
v___x_4327_ = l_Lean_Fmt_fmt(v_tildeTk_4326_, v_a_4314_, v_a_4324_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4341_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
v_a_4329_ = lean_ctor_get(v___x_4327_, 1);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4331_ = v___x_4327_;
v_isShared_4332_ = v_isSharedCheck_4341_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_inc(v_a_4328_);
lean_dec(v___x_4327_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4341_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4339_; 
v___x_4333_ = lean_unsigned_to_nat(2u);
v___x_4334_ = lean_mk_empty_array_with_capacity(v___x_4333_);
v___x_4335_ = lean_array_push(v___x_4334_, v_a_4323_);
v___x_4336_ = lean_array_push(v___x_4335_, v_a_4328_);
v___x_4337_ = l_Lean_Fmt_Layouts_atomic(v___x_4336_);
lean_dec_ref(v___x_4336_);
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 0, v___x_4337_);
v___x_4339_ = v___x_4331_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_a_4329_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
else
{
lean_dec(v_a_4323_);
return v___x_4327_;
}
}
else
{
lean_dec(v_x_4313_);
return v___x_4322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSymIntrosLight___boxed(lean_object* v_x_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_Fmt_fmtGrindSymIntrosLight(v_x_4342_, v_a_4343_, v_a_4344_);
lean_dec_ref(v_a_4343_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1(){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4352_ = l_Lean_Fmt_fmtAttribute;
v___x_4353_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSymIntrosLight___closed__1));
v___x_4354_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___closed__1));
v___x_4355_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSymIntrosLight___boxed), 3, 0);
v___x_4356_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4352_, v___x_4353_, v___x_4354_, v___x_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1___boxed(lean_object* v_a_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1();
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSimp(lean_object* v_x_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v___x_4369_; uint8_t v___x_4370_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; 
v___x_4369_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSimp___closed__1));
lean_inc(v_x_4366_);
v___x_4370_ = l_Lean_Syntax_isOfKind(v_x_4366_, v___x_4369_);
if (v___x_4370_ == 0)
{
lean_object* v___x_4412_; lean_object* v___x_4413_; 
lean_dec(v_x_4366_);
v___x_4412_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
lean_ctor_set(v___x_4413_, 1, v_a_4368_);
return v___x_4413_;
}
else
{
lean_object* v___x_4414_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v_simpTk_4432_; lean_object* v___y_4434_; lean_object* v_lbTk_x3f_4435_; lean_object* v_thms_x3f_4436_; lean_object* v_rbTk_x3f_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___x_4454_; lean_object* v_variant_x3f_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___x_4474_; uint8_t v___x_4475_; 
v___x_4414_ = lean_unsigned_to_nat(0u);
v_simpTk_4432_ = l_Lean_Syntax_getArg(v_x_4366_, v___x_4414_);
v___x_4454_ = lean_unsigned_to_nat(1u);
v___x_4474_ = l_Lean_Syntax_getArg(v_x_4366_, v___x_4454_);
v___x_4475_ = l_Lean_Syntax_isNone(v___x_4474_);
if (v___x_4475_ == 0)
{
uint8_t v___x_4476_; 
lean_inc(v___x_4474_);
v___x_4476_ = l_Lean_Syntax_matchesNull(v___x_4474_, v___x_4454_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
lean_dec(v___x_4474_);
lean_dec(v_simpTk_4432_);
lean_dec(v_x_4366_);
v___x_4477_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
lean_ctor_set(v___x_4478_, 1, v_a_4368_);
return v___x_4478_;
}
else
{
lean_object* v_variant_x3f_4479_; lean_object* v___x_4480_; uint8_t v___x_4481_; 
v_variant_x3f_4479_ = l_Lean_Syntax_getArg(v___x_4474_, v___x_4414_);
lean_dec(v___x_4474_);
v___x_4480_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__3));
lean_inc(v_variant_x3f_4479_);
v___x_4481_ = l_Lean_Syntax_isOfKind(v_variant_x3f_4479_, v___x_4480_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
lean_dec(v_variant_x3f_4479_);
lean_dec(v_simpTk_4432_);
lean_dec(v_x_4366_);
v___x_4482_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
lean_ctor_set(v___x_4483_, 1, v_a_4368_);
return v___x_4483_;
}
else
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4484_, 0, v_variant_x3f_4479_);
v_variant_x3f_4456_ = v___x_4484_;
v___y_4457_ = v_a_4367_;
v___y_4458_ = v_a_4368_;
goto v___jp_4455_;
}
}
}
else
{
lean_object* v___x_4485_; 
lean_dec(v___x_4474_);
v___x_4485_ = lean_box(0);
v_variant_x3f_4456_ = v___x_4485_;
v___y_4457_ = v_a_4367_;
v___y_4458_ = v_a_4368_;
goto v___jp_4455_;
}
v___jp_4415_:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_Fmt_fmt_x3f(v___y_4422_, v___y_4421_, v___y_4419_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v_a_4425_; lean_object* v___x_4426_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
v_a_4425_ = lean_ctor_get(v___x_4423_, 1);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4423_, 2);
v___x_4426_ = l_Lean_Fmt_fmt_x3f(v___y_4416_, v___y_4421_, v_a_4425_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v_a_4428_; lean_object* v___x_4429_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
v_a_4428_ = lean_ctor_get(v___x_4426_, 1);
lean_inc(v_a_4428_);
lean_dec_ref_known(v___x_4426_, 2);
v___x_4429_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__2));
if (lean_obj_tag(v___y_4420_) == 0)
{
lean_object* v___x_4430_; 
v___x_4430_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__3));
v___y_4372_ = v___x_4429_;
v___y_4373_ = v___y_4417_;
v___y_4374_ = v_a_4428_;
v___y_4375_ = v_a_4427_;
v___y_4376_ = v___y_4418_;
v___y_4377_ = v_a_4424_;
v___y_4378_ = v___y_4421_;
v___y_4379_ = v___x_4430_;
goto v___jp_4371_;
}
else
{
lean_object* v_val_4431_; 
v_val_4431_ = lean_ctor_get(v___y_4420_, 0);
lean_inc(v_val_4431_);
lean_dec_ref_known(v___y_4420_, 1);
v___y_4372_ = v___x_4429_;
v___y_4373_ = v___y_4417_;
v___y_4374_ = v_a_4428_;
v___y_4375_ = v_a_4427_;
v___y_4376_ = v___y_4418_;
v___y_4377_ = v_a_4424_;
v___y_4378_ = v___y_4421_;
v___y_4379_ = v_val_4431_;
goto v___jp_4371_;
}
}
else
{
lean_dec(v_a_4424_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
return v___x_4426_;
}
}
else
{
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec(v___y_4416_);
return v___x_4423_;
}
}
v___jp_4433_:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_Lean_Fmt_fmt(v_simpTk_4432_, v___y_4438_, v___y_4439_);
if (lean_obj_tag(v___x_4440_) == 0)
{
if (lean_obj_tag(v___y_4434_) == 0)
{
lean_object* v_a_4441_; lean_object* v_a_4442_; lean_object* v___x_4443_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
v_a_4442_ = lean_ctor_get(v___x_4440_, 1);
lean_inc(v_a_4442_);
lean_dec_ref_known(v___x_4440_, 2);
v___x_4443_ = lean_box(0);
v___y_4416_ = v_lbTk_x3f_4435_;
v___y_4417_ = v_rbTk_x3f_4437_;
v___y_4418_ = v_a_4441_;
v___y_4419_ = v_a_4442_;
v___y_4420_ = v_thms_x3f_4436_;
v___y_4421_ = v___y_4438_;
v___y_4422_ = v___x_4443_;
goto v___jp_4415_;
}
else
{
lean_object* v_a_4444_; lean_object* v_a_4445_; lean_object* v_val_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
v_a_4444_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4444_);
v_a_4445_ = lean_ctor_get(v___x_4440_, 1);
lean_inc(v_a_4445_);
lean_dec_ref_known(v___x_4440_, 2);
v_val_4446_ = lean_ctor_get(v___y_4434_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___y_4434_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___y_4434_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_val_4446_);
lean_dec(v___y_4434_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_val_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
v___y_4416_ = v_lbTk_x3f_4435_;
v___y_4417_ = v_rbTk_x3f_4437_;
v___y_4418_ = v_a_4444_;
v___y_4419_ = v_a_4445_;
v___y_4420_ = v_thms_x3f_4436_;
v___y_4421_ = v___y_4438_;
v___y_4422_ = v___x_4451_;
goto v___jp_4415_;
}
}
}
}
else
{
lean_dec(v_rbTk_x3f_4437_);
lean_dec(v_thms_x3f_4436_);
lean_dec(v_lbTk_x3f_4435_);
lean_dec(v___y_4434_);
return v___x_4440_;
}
}
v___jp_4455_:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; uint8_t v___x_4461_; 
v___x_4459_ = lean_unsigned_to_nat(2u);
v___x_4460_ = l_Lean_Syntax_getArg(v_x_4366_, v___x_4459_);
lean_dec(v_x_4366_);
v___x_4461_ = l_Lean_Syntax_isNone(v___x_4460_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; uint8_t v___x_4463_; 
v___x_4462_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_4460_);
v___x_4463_ = l_Lean_Syntax_matchesNull(v___x_4460_, v___x_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
lean_dec(v___x_4460_);
lean_dec(v_variant_x3f_4456_);
lean_dec(v_simpTk_4432_);
v___x_4464_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
lean_ctor_set(v___x_4465_, 1, v___y_4458_);
return v___x_4465_;
}
else
{
lean_object* v_lbTk_x3f_4466_; lean_object* v___x_4467_; lean_object* v_rbTk_x3f_4468_; lean_object* v_thms_x3f_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v_lbTk_x3f_4466_ = l_Lean_Syntax_getArg(v___x_4460_, v___x_4414_);
v___x_4467_ = l_Lean_Syntax_getArg(v___x_4460_, v___x_4454_);
v_rbTk_x3f_4468_ = l_Lean_Syntax_getArg(v___x_4460_, v___x_4459_);
lean_dec(v___x_4460_);
v_thms_x3f_4469_ = l_Lean_Syntax_getArgs(v___x_4467_);
lean_dec(v___x_4467_);
v___x_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4470_, 0, v_lbTk_x3f_4466_);
v___x_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4471_, 0, v_thms_x3f_4469_);
v___x_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4472_, 0, v_rbTk_x3f_4468_);
v___y_4434_ = v_variant_x3f_4456_;
v_lbTk_x3f_4435_ = v___x_4470_;
v_thms_x3f_4436_ = v___x_4471_;
v_rbTk_x3f_4437_ = v___x_4472_;
v___y_4438_ = v___y_4457_;
v___y_4439_ = v___y_4458_;
goto v___jp_4433_;
}
}
else
{
lean_object* v___x_4473_; 
lean_dec(v___x_4460_);
v___x_4473_ = lean_box(0);
v___y_4434_ = v_variant_x3f_4456_;
v_lbTk_x3f_4435_ = v___x_4473_;
v_thms_x3f_4436_ = v___x_4473_;
v_rbTk_x3f_4437_ = v___x_4473_;
v___y_4438_ = v___y_4457_;
v___y_4439_ = v___y_4458_;
goto v___jp_4433_;
}
}
}
v___jp_4371_:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_4379_, v___y_4378_, v___y_4374_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v_a_4382_; lean_object* v___x_4383_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
v_a_4382_ = lean_ctor_get(v___x_4380_, 1);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4380_, 2);
v___x_4383_ = l_Lean_Fmt_fmt_x3f(v___y_4373_, v___y_4378_, v_a_4382_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4402_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
v_a_4385_ = lean_ctor_get(v___x_4383_, 1);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4387_ = v___x_4383_;
v_isShared_4388_ = v_isSharedCheck_4402_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_inc(v_a_4384_);
lean_dec(v___x_4383_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4402_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
uint8_t v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4389_ = 0;
v___x_4390_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4390_, 0, v___x_4389_);
lean_ctor_set_uint8(v___x_4390_, 1, v___x_4370_);
lean_inc_ref(v___y_4372_);
v___x_4391_ = l_Lean_Fmt_Layouts_collection(v___y_4372_, v___y_4375_, v_a_4381_, v_a_4384_, v___x_4390_);
lean_dec(v_a_4381_);
v___x_4392_ = lean_unsigned_to_nat(3u);
v___x_4393_ = lean_mk_empty_array_with_capacity(v___x_4392_);
v___x_4394_ = lean_array_push(v___x_4393_, v___y_4376_);
v___x_4395_ = lean_array_push(v___x_4394_, v___y_4377_);
v___x_4396_ = lean_array_push(v___x_4395_, v___x_4391_);
v___x_4397_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4397_, 0, v___x_4370_);
lean_ctor_set_uint8(v___x_4397_, 1, v___x_4389_);
lean_ctor_set_uint8(v___x_4397_, 2, v___x_4389_);
lean_ctor_set_uint8(v___x_4397_, 3, v___x_4389_);
v___x_4398_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4396_, v___x_4397_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4398_);
v___x_4400_ = v___x_4387_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_a_4385_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
else
{
lean_dec(v_a_4381_);
lean_dec_ref(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec_ref(v___y_4375_);
return v___x_4383_;
}
}
else
{
lean_object* v_a_4403_; lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec_ref(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4373_);
v_a_4403_ = lean_ctor_get(v___x_4380_, 0);
v_a_4404_ = lean_ctor_get(v___x_4380_, 1);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4380_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_inc(v_a_4403_);
lean_dec(v___x_4380_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4403_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSimp___boxed(lean_object* v_x_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_Fmt_fmtGrindSimp(v_x_4486_, v_a_4487_, v_a_4488_);
lean_dec_ref(v_a_4487_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1(){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4496_ = l_Lean_Fmt_fmtAttribute;
v___x_4497_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSimp___closed__1));
v___x_4498_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___closed__1));
v___x_4499_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSimp___boxed), 3, 0);
v___x_4500_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4496_, v___x_4497_, v___x_4498_, v___x_4499_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1___boxed(lean_object* v_a_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1();
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDSimp___lam__0(lean_object* v_e_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
uint8_t v___x_4506_; 
v___x_4506_ = l_Lean_Syntax_isIdent(v_e_4503_);
if (v___x_4506_ == 0)
{
lean_object* v___x_4507_; 
v___x_4507_ = l_Lean_Fmt_fmtAtomic(v_e_4503_, v___y_4504_, v___y_4505_);
return v___x_4507_;
}
else
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_Fmt_fmt(v_e_4503_, v___y_4504_, v___y_4505_);
return v___x_4508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDSimp___lam__0___boxed(lean_object* v_e_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_Fmt_fmtGrindDSimp___lam__0(v_e_4509_, v___y_4510_, v___y_4511_);
lean_dec_ref(v___y_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDSimp(lean_object* v_x_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4527_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDSimp___closed__1));
lean_inc(v_x_4524_);
v___x_4528_ = l_Lean_Syntax_isOfKind(v_x_4524_, v___x_4527_);
if (v___x_4528_ == 0)
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
lean_dec(v_x_4524_);
v___x_4529_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
lean_ctor_set(v___x_4530_, 1, v_a_4526_);
return v___x_4530_;
}
else
{
lean_object* v___f_4531_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___x_4574_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v_dsimpTk_4593_; lean_object* v___y_4595_; lean_object* v_lbTk_x3f_4596_; lean_object* v_thms_x3f_4597_; lean_object* v_rbTk_x3f_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___x_4615_; lean_object* v_variant_x3f_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
v___f_4531_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDSimp___closed__2));
v___x_4574_ = lean_unsigned_to_nat(0u);
v_dsimpTk_4593_ = l_Lean_Syntax_getArg(v_x_4524_, v___x_4574_);
v___x_4615_ = lean_unsigned_to_nat(1u);
v___x_4635_ = l_Lean_Syntax_getArg(v_x_4524_, v___x_4615_);
v___x_4636_ = l_Lean_Syntax_isNone(v___x_4635_);
if (v___x_4636_ == 0)
{
uint8_t v___x_4637_; 
lean_inc(v___x_4635_);
v___x_4637_ = l_Lean_Syntax_matchesNull(v___x_4635_, v___x_4615_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
lean_dec(v___x_4635_);
lean_dec(v_dsimpTk_4593_);
lean_dec(v_x_4524_);
v___x_4638_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
lean_ctor_set(v___x_4639_, 1, v_a_4526_);
return v___x_4639_;
}
else
{
lean_object* v_variant_x3f_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; 
v_variant_x3f_4640_ = l_Lean_Syntax_getArg(v___x_4635_, v___x_4574_);
lean_dec(v___x_4635_);
v___x_4641_ = ((lean_object*)(l_Lean_Fmt_fmtGrindErase___closed__3));
lean_inc(v_variant_x3f_4640_);
v___x_4642_ = l_Lean_Syntax_isOfKind(v_variant_x3f_4640_, v___x_4641_);
if (v___x_4642_ == 0)
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
lean_dec(v_variant_x3f_4640_);
lean_dec(v_dsimpTk_4593_);
lean_dec(v_x_4524_);
v___x_4643_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
lean_ctor_set(v___x_4644_, 1, v_a_4526_);
return v___x_4644_;
}
else
{
lean_object* v___x_4645_; 
v___x_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4645_, 0, v_variant_x3f_4640_);
v_variant_x3f_4617_ = v___x_4645_;
v___y_4618_ = v_a_4525_;
v___y_4619_ = v_a_4526_;
goto v___jp_4616_;
}
}
}
else
{
lean_object* v___x_4646_; 
lean_dec(v___x_4635_);
v___x_4646_ = lean_box(0);
v_variant_x3f_4617_ = v___x_4646_;
v___y_4618_ = v_a_4525_;
v___y_4619_ = v_a_4526_;
goto v___jp_4616_;
}
v___jp_4532_:
{
lean_object* v___x_4542_; 
lean_inc(v___y_4537_);
v___x_4542_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v___f_4531_, v___y_4537_, v___y_4541_, v___y_4536_, v___y_4534_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v_a_4544_; lean_object* v___x_4545_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_a_4543_);
v_a_4544_ = lean_ctor_get(v___x_4542_, 1);
lean_inc(v_a_4544_);
lean_dec_ref_known(v___x_4542_, 2);
v___x_4545_ = l_Lean_Fmt_fmt_x3f(v___y_4535_, v___y_4536_, v_a_4544_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4564_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
v_a_4547_ = lean_ctor_get(v___x_4545_, 1);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4549_ = v___x_4545_;
v_isShared_4550_ = v_isSharedCheck_4564_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_inc(v_a_4546_);
lean_dec(v___x_4545_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4564_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
uint8_t v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4562_; 
v___x_4551_ = 0;
v___x_4552_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4552_, 0, v___x_4551_);
lean_ctor_set_uint8(v___x_4552_, 1, v___x_4528_);
lean_inc_ref(v___y_4540_);
v___x_4553_ = l_Lean_Fmt_Layouts_collection(v___y_4540_, v___y_4539_, v_a_4543_, v_a_4546_, v___x_4552_);
lean_dec(v_a_4543_);
v___x_4554_ = lean_unsigned_to_nat(3u);
v___x_4555_ = lean_mk_empty_array_with_capacity(v___x_4554_);
v___x_4556_ = lean_array_push(v___x_4555_, v___y_4533_);
v___x_4557_ = lean_array_push(v___x_4556_, v___y_4538_);
v___x_4558_ = lean_array_push(v___x_4557_, v___x_4553_);
v___x_4559_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4559_, 0, v___x_4528_);
lean_ctor_set_uint8(v___x_4559_, 1, v___x_4551_);
lean_ctor_set_uint8(v___x_4559_, 2, v___x_4551_);
lean_ctor_set_uint8(v___x_4559_, 3, v___x_4551_);
v___x_4560_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4558_, v___x_4559_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 0, v___x_4560_);
v___x_4562_ = v___x_4549_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v___x_4560_);
lean_ctor_set(v_reuseFailAlloc_4563_, 1, v_a_4547_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
else
{
lean_dec(v_a_4543_);
lean_dec_ref(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec_ref(v___y_4533_);
return v___x_4545_;
}
}
else
{
lean_object* v_a_4565_; lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec_ref(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4533_);
v_a_4565_ = lean_ctor_get(v___x_4542_, 0);
v_a_4566_ = lean_ctor_get(v___x_4542_, 1);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4542_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_inc(v_a_4565_);
lean_dec(v___x_4542_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4565_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
v___jp_4575_:
{
lean_object* v___x_4583_; 
v___x_4583_ = l_Lean_Fmt_fmt_x3f(v___y_4582_, v___y_4578_, v___y_4581_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v_a_4585_; lean_object* v___x_4586_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
lean_inc(v_a_4584_);
v_a_4585_ = lean_ctor_get(v___x_4583_, 1);
lean_inc(v_a_4585_);
lean_dec_ref_known(v___x_4583_, 2);
v___x_4586_ = l_Lean_Fmt_fmt_x3f(v___y_4580_, v___y_4578_, v_a_4585_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v_a_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
v_a_4588_ = lean_ctor_get(v___x_4586_, 1);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___x_4586_, 2);
v___x_4589_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__2));
v___x_4590_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDSimp___closed__4));
if (lean_obj_tag(v___y_4579_) == 0)
{
lean_object* v___x_4591_; 
v___x_4591_ = ((lean_object*)(l_Lean_Fmt_fmtGrindInstantiate___closed__3));
v___y_4533_ = v___y_4576_;
v___y_4534_ = v_a_4588_;
v___y_4535_ = v___y_4577_;
v___y_4536_ = v___y_4578_;
v___y_4537_ = v___x_4590_;
v___y_4538_ = v_a_4584_;
v___y_4539_ = v_a_4587_;
v___y_4540_ = v___x_4589_;
v___y_4541_ = v___x_4591_;
goto v___jp_4532_;
}
else
{
lean_object* v_val_4592_; 
v_val_4592_ = lean_ctor_get(v___y_4579_, 0);
lean_inc(v_val_4592_);
lean_dec_ref_known(v___y_4579_, 1);
v___y_4533_ = v___y_4576_;
v___y_4534_ = v_a_4588_;
v___y_4535_ = v___y_4577_;
v___y_4536_ = v___y_4578_;
v___y_4537_ = v___x_4590_;
v___y_4538_ = v_a_4584_;
v___y_4539_ = v_a_4587_;
v___y_4540_ = v___x_4589_;
v___y_4541_ = v_val_4592_;
goto v___jp_4532_;
}
}
else
{
lean_dec(v_a_4584_);
lean_dec(v___y_4579_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
return v___x_4586_;
}
}
else
{
lean_dec(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
return v___x_4583_;
}
}
v___jp_4594_:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Lean_Fmt_fmt(v_dsimpTk_4593_, v___y_4599_, v___y_4600_);
if (lean_obj_tag(v___x_4601_) == 0)
{
if (lean_obj_tag(v___y_4595_) == 0)
{
lean_object* v_a_4602_; lean_object* v_a_4603_; lean_object* v___x_4604_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
v_a_4603_ = lean_ctor_get(v___x_4601_, 1);
lean_inc(v_a_4603_);
lean_dec_ref_known(v___x_4601_, 2);
v___x_4604_ = lean_box(0);
v___y_4576_ = v_a_4602_;
v___y_4577_ = v_rbTk_x3f_4598_;
v___y_4578_ = v___y_4599_;
v___y_4579_ = v_thms_x3f_4597_;
v___y_4580_ = v_lbTk_x3f_4596_;
v___y_4581_ = v_a_4603_;
v___y_4582_ = v___x_4604_;
goto v___jp_4575_;
}
else
{
lean_object* v_a_4605_; lean_object* v_a_4606_; lean_object* v_val_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
v_a_4605_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4605_);
v_a_4606_ = lean_ctor_get(v___x_4601_, 1);
lean_inc(v_a_4606_);
lean_dec_ref_known(v___x_4601_, 2);
v_val_4607_ = lean_ctor_get(v___y_4595_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___y_4595_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___y_4595_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_val_4607_);
lean_dec(v___y_4595_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_val_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
v___y_4576_ = v_a_4605_;
v___y_4577_ = v_rbTk_x3f_4598_;
v___y_4578_ = v___y_4599_;
v___y_4579_ = v_thms_x3f_4597_;
v___y_4580_ = v_lbTk_x3f_4596_;
v___y_4581_ = v_a_4606_;
v___y_4582_ = v___x_4612_;
goto v___jp_4575_;
}
}
}
}
else
{
lean_dec(v_rbTk_x3f_4598_);
lean_dec(v_thms_x3f_4597_);
lean_dec(v_lbTk_x3f_4596_);
lean_dec(v___y_4595_);
return v___x_4601_;
}
}
v___jp_4616_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; uint8_t v___x_4622_; 
v___x_4620_ = lean_unsigned_to_nat(2u);
v___x_4621_ = l_Lean_Syntax_getArg(v_x_4524_, v___x_4620_);
lean_dec(v_x_4524_);
v___x_4622_ = l_Lean_Syntax_isNone(v___x_4621_);
if (v___x_4622_ == 0)
{
lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4623_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_4621_);
v___x_4624_ = l_Lean_Syntax_matchesNull(v___x_4621_, v___x_4623_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
lean_dec(v___x_4621_);
lean_dec(v_variant_x3f_4617_);
lean_dec(v_dsimpTk_4593_);
v___x_4625_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
lean_ctor_set(v___x_4626_, 1, v___y_4619_);
return v___x_4626_;
}
else
{
lean_object* v_lbTk_x3f_4627_; lean_object* v___x_4628_; lean_object* v_rbTk_x3f_4629_; lean_object* v_thms_x3f_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v_lbTk_x3f_4627_ = l_Lean_Syntax_getArg(v___x_4621_, v___x_4574_);
v___x_4628_ = l_Lean_Syntax_getArg(v___x_4621_, v___x_4615_);
v_rbTk_x3f_4629_ = l_Lean_Syntax_getArg(v___x_4621_, v___x_4620_);
lean_dec(v___x_4621_);
v_thms_x3f_4630_ = l_Lean_Syntax_getArgs(v___x_4628_);
lean_dec(v___x_4628_);
v___x_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4631_, 0, v_lbTk_x3f_4627_);
v___x_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4632_, 0, v_thms_x3f_4630_);
v___x_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4633_, 0, v_rbTk_x3f_4629_);
v___y_4595_ = v_variant_x3f_4617_;
v_lbTk_x3f_4596_ = v___x_4631_;
v_thms_x3f_4597_ = v___x_4632_;
v_rbTk_x3f_4598_ = v___x_4633_;
v___y_4599_ = v___y_4618_;
v___y_4600_ = v___y_4619_;
goto v___jp_4594_;
}
}
else
{
lean_object* v___x_4634_; 
lean_dec(v___x_4621_);
v___x_4634_ = lean_box(0);
v___y_4595_ = v_variant_x3f_4617_;
v_lbTk_x3f_4596_ = v___x_4634_;
v_thms_x3f_4597_ = v___x_4634_;
v_rbTk_x3f_4598_ = v___x_4634_;
v___y_4599_ = v___y_4618_;
v___y_4600_ = v___y_4619_;
goto v___jp_4594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDSimp___boxed(lean_object* v_x_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_Fmt_fmtGrindDSimp(v_x_4647_, v_a_4648_, v_a_4649_);
lean_dec_ref(v_a_4648_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1(){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4657_ = l_Lean_Fmt_fmtAttribute;
v___x_4658_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDSimp___closed__1));
v___x_4659_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___closed__1));
v___x_4660_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindDSimp___boxed), 3, 0);
v___x_4661_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4657_, v___x_4658_, v___x_4659_, v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1___boxed(lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1();
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRw(lean_object* v_x_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
lean_object* v___x_4680_; uint8_t v___x_4681_; 
v___x_4680_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRw___closed__1));
lean_inc(v_x_4677_);
v___x_4681_ = l_Lean_Syntax_isOfKind(v_x_4677_, v___x_4680_);
if (v___x_4681_ == 0)
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
lean_dec(v_x_4677_);
v___x_4682_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
lean_ctor_set(v___x_4683_, 1, v_a_4679_);
return v___x_4683_;
}
else
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; 
v___x_4684_ = lean_unsigned_to_nat(1u);
v___x_4685_ = l_Lean_Syntax_getArg(v_x_4677_, v___x_4684_);
v___x_4686_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRw___closed__3));
lean_inc(v___x_4685_);
v___x_4687_ = l_Lean_Syntax_isOfKind(v___x_4685_, v___x_4686_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; lean_object* v___x_4689_; 
lean_dec(v___x_4685_);
lean_dec(v_x_4677_);
v___x_4688_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
lean_ctor_set(v___x_4689_, 1, v_a_4679_);
return v___x_4689_;
}
else
{
lean_object* v___x_4690_; lean_object* v_rwTk_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4690_ = lean_unsigned_to_nat(0u);
v_rwTk_4691_ = l_Lean_Syntax_getArg(v_x_4677_, v___x_4690_);
lean_dec(v_x_4677_);
v___x_4692_ = lean_box(0);
v___x_4693_ = l_Lean_Fmt_fmtRwLike(v_rwTk_4691_, v___x_4692_, v___x_4685_, v___x_4692_, v_a_4678_, v_a_4679_);
return v___x_4693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindRw___boxed(lean_object* v_x_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_Fmt_fmtGrindRw(v_x_4694_, v_a_4695_, v_a_4696_);
lean_dec_ref(v_a_4695_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1(){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4704_ = l_Lean_Fmt_fmtAttribute;
v___x_4705_ = ((lean_object*)(l_Lean_Fmt_fmtGrindRw___closed__1));
v___x_4706_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___closed__1));
v___x_4707_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindRw___boxed), 3, 0);
v___x_4708_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4704_, v___x_4705_, v___x_4706_, v___x_4707_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1___boxed(lean_object* v_a_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1();
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0(size_t v_sz_4711_, size_t v_i_4712_, lean_object* v_bs_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
uint8_t v___x_4716_; 
v___x_4716_ = lean_usize_dec_lt(v_i_4712_, v_sz_4711_);
if (v___x_4716_ == 0)
{
lean_object* v___x_4717_; 
v___x_4717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4717_, 0, v_bs_4713_);
lean_ctor_set(v___x_4717_, 1, v___y_4715_);
return v___x_4717_;
}
else
{
lean_object* v_v_4718_; lean_object* v___x_4719_; 
v_v_4718_ = lean_array_uget_borrowed(v_bs_4713_, v_i_4712_);
lean_inc(v_v_4718_);
v___x_4719_ = l_Lean_Fmt_fmt(v_v_4718_, v___y_4714_, v___y_4715_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v_a_4721_; lean_object* v___x_4722_; lean_object* v_bs_x27_4723_; size_t v___x_4724_; size_t v___x_4725_; lean_object* v___x_4726_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
v_a_4721_ = lean_ctor_get(v___x_4719_, 1);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4719_, 2);
v___x_4722_ = lean_unsigned_to_nat(0u);
v_bs_x27_4723_ = lean_array_uset(v_bs_4713_, v_i_4712_, v___x_4722_);
v___x_4724_ = ((size_t)1ULL);
v___x_4725_ = lean_usize_add(v_i_4712_, v___x_4724_);
v___x_4726_ = lean_array_uset(v_bs_x27_4723_, v_i_4712_, v_a_4720_);
v_i_4712_ = v___x_4725_;
v_bs_4713_ = v___x_4726_;
v___y_4715_ = v_a_4721_;
goto _start;
}
else
{
lean_object* v_a_4728_; lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
lean_dec_ref(v_bs_4713_);
v_a_4728_ = lean_ctor_get(v___x_4719_, 0);
v_a_4729_ = lean_ctor_get(v___x_4719_, 1);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4719_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_inc(v_a_4728_);
lean_dec(v___x_4719_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4728_);
lean_ctor_set(v_reuseFailAlloc_4735_, 1, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0___boxed(lean_object* v_sz_4737_, lean_object* v_i_4738_, lean_object* v_bs_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
size_t v_sz_boxed_4742_; size_t v_i_boxed_4743_; lean_object* v_res_4744_; 
v_sz_boxed_4742_ = lean_unbox_usize(v_sz_4737_);
lean_dec(v_sz_4737_);
v_i_boxed_4743_ = lean_unbox_usize(v_i_4738_);
lean_dec(v_i_4738_);
v_res_4744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0(v_sz_boxed_4742_, v_i_boxed_4743_, v_bs_4739_, v___y_4740_, v___y_4741_);
lean_dec_ref(v___y_4740_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvNormalize(lean_object* v_x_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4767_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__1));
lean_inc(v_x_4764_);
v___x_4768_ = l_Lean_Syntax_isOfKind(v_x_4764_, v___x_4767_);
if (v___x_4768_ == 0)
{
lean_object* v___x_4769_; lean_object* v___x_4770_; 
lean_dec(v_x_4764_);
v___x_4769_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4770_, 0, v___x_4769_);
lean_ctor_set(v___x_4770_, 1, v_a_4766_);
return v___x_4770_;
}
else
{
lean_object* v___x_4771_; lean_object* v_cfg_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; lean_object* v___y_4776_; lean_object* v___y_4777_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v___y_4780_; 
v___x_4771_ = lean_unsigned_to_nat(1u);
v_cfg_4772_ = l_Lean_Syntax_getArg(v_x_4764_, v___x_4771_);
v___x_4773_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__3));
lean_inc(v_cfg_4772_);
v___x_4774_ = l_Lean_Syntax_isOfKind(v_cfg_4772_, v___x_4773_);
if (v___x_4774_ == 0)
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
lean_dec(v_cfg_4772_);
lean_dec(v_x_4764_);
v___x_4804_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4804_);
lean_ctor_set(v___x_4805_, 1, v_a_4766_);
return v___x_4805_;
}
else
{
lean_object* v___x_4806_; lean_object* v_bvNormalizeTk_4807_; lean_object* v_types_x3f_4809_; lean_object* v___y_4810_; lean_object* v___y_4811_; lean_object* v___x_4852_; lean_object* v___x_4853_; uint8_t v___x_4854_; 
v___x_4806_ = lean_unsigned_to_nat(0u);
v_bvNormalizeTk_4807_ = l_Lean_Syntax_getArg(v_x_4764_, v___x_4806_);
v___x_4852_ = lean_unsigned_to_nat(2u);
v___x_4853_ = l_Lean_Syntax_getArg(v_x_4764_, v___x_4852_);
lean_dec(v_x_4764_);
v___x_4854_ = l_Lean_Syntax_isNone(v___x_4853_);
if (v___x_4854_ == 0)
{
uint8_t v___x_4855_; 
lean_inc(v___x_4853_);
v___x_4855_ = l_Lean_Syntax_matchesNull(v___x_4853_, v___x_4771_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4856_; lean_object* v___x_4857_; 
lean_dec(v___x_4853_);
lean_dec(v_bvNormalizeTk_4807_);
lean_dec(v_cfg_4772_);
v___x_4856_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4856_);
lean_ctor_set(v___x_4857_, 1, v_a_4766_);
return v___x_4857_;
}
else
{
lean_object* v_types_x3f_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v_types_x3f_4858_ = l_Lean_Syntax_getArg(v___x_4853_, v___x_4806_);
lean_dec(v___x_4853_);
v___x_4859_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__5));
lean_inc(v_types_x3f_4858_);
v___x_4860_ = l_Lean_Syntax_isOfKind(v_types_x3f_4858_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; lean_object* v___x_4862_; 
lean_dec(v_types_x3f_4858_);
lean_dec(v_bvNormalizeTk_4807_);
lean_dec(v_cfg_4772_);
v___x_4861_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
lean_ctor_set(v___x_4862_, 1, v_a_4766_);
return v___x_4862_;
}
else
{
lean_object* v___x_4863_; 
v___x_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4863_, 0, v_types_x3f_4858_);
v_types_x3f_4809_ = v___x_4863_;
v___y_4810_ = v_a_4765_;
v___y_4811_ = v_a_4766_;
goto v___jp_4808_;
}
}
}
else
{
lean_object* v___x_4864_; 
lean_dec(v___x_4853_);
v___x_4864_ = lean_box(0);
v_types_x3f_4809_ = v___x_4864_;
v___y_4810_ = v_a_4765_;
v___y_4811_ = v_a_4766_;
goto v___jp_4808_;
}
v___jp_4808_:
{
lean_object* v___x_4812_; 
v___x_4812_ = l_Lean_Fmt_fmt(v_bvNormalizeTk_4807_, v___y_4810_, v___y_4811_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; lean_object* v_a_4814_; lean_object* v___x_4815_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
lean_inc(v_a_4813_);
v_a_4814_ = lean_ctor_get(v___x_4812_, 1);
lean_inc(v_a_4814_);
lean_dec_ref_known(v___x_4812_, 2);
v___x_4815_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_4772_, v_a_4814_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v_a_4817_; size_t v_sz_4818_; size_t v___x_4819_; lean_object* v___x_4820_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc(v_a_4816_);
v_a_4817_ = lean_ctor_get(v___x_4815_, 1);
lean_inc(v_a_4817_);
lean_dec_ref_known(v___x_4815_, 2);
v_sz_4818_ = lean_array_size(v_a_4816_);
v___x_4819_ = ((size_t)0ULL);
v___x_4820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0(v_sz_4818_, v___x_4819_, v_a_4816_, v___y_4810_, v_a_4817_);
if (lean_obj_tag(v___x_4820_) == 0)
{
if (lean_obj_tag(v_types_x3f_4809_) == 0)
{
lean_object* v_a_4821_; lean_object* v_a_4822_; lean_object* v___x_4823_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4821_);
v_a_4822_ = lean_ctor_get(v___x_4820_, 1);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4820_, 2);
v___x_4823_ = lean_box(0);
v___y_4776_ = v_a_4813_;
v___y_4777_ = v___y_4810_;
v___y_4778_ = v_a_4822_;
v___y_4779_ = v_a_4821_;
v___y_4780_ = v___x_4823_;
goto v___jp_4775_;
}
else
{
lean_object* v_a_4824_; lean_object* v_a_4825_; lean_object* v_val_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
v_a_4824_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4824_);
v_a_4825_ = lean_ctor_get(v___x_4820_, 1);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4820_, 2);
v_val_4826_ = lean_ctor_get(v_types_x3f_4809_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v_types_x3f_4809_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v_types_x3f_4809_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_val_4826_);
lean_dec(v_types_x3f_4809_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_val_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
v___y_4776_ = v_a_4813_;
v___y_4777_ = v___y_4810_;
v___y_4778_ = v_a_4825_;
v___y_4779_ = v_a_4824_;
v___y_4780_ = v___x_4831_;
goto v___jp_4775_;
}
}
}
}
else
{
lean_object* v_a_4834_; lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
lean_dec(v_a_4813_);
lean_dec(v_types_x3f_4809_);
v_a_4834_ = lean_ctor_get(v___x_4820_, 0);
v_a_4835_ = lean_ctor_get(v___x_4820_, 1);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4820_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_inc(v_a_4834_);
lean_dec(v___x_4820_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4834_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
else
{
lean_object* v_a_4843_; lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
lean_dec(v_a_4813_);
lean_dec(v_types_x3f_4809_);
v_a_4843_ = lean_ctor_get(v___x_4815_, 0);
v_a_4844_ = lean_ctor_get(v___x_4815_, 1);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___x_4815_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_inc(v_a_4843_);
lean_dec(v___x_4815_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4843_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_a_4844_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
else
{
lean_dec(v_types_x3f_4809_);
lean_dec(v_cfg_4772_);
return v___x_4812_;
}
}
}
v___jp_4775_:
{
lean_object* v___x_4781_; 
v___x_4781_ = l_Lean_Fmt_fmt_x3f(v___y_4780_, v___y_4777_, v___y_4778_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4803_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
v_a_4783_ = lean_ctor_get(v___x_4781_, 1);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4785_ = v___x_4781_;
v_isShared_4786_ = v_isSharedCheck_4803_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_inc(v_a_4782_);
lean_dec(v___x_4781_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4803_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4787_ = lean_mk_empty_array_with_capacity(v___x_4771_);
v___x_4788_ = lean_array_push(v___x_4787_, v___y_4776_);
v___x_4789_ = l_Array_append___redArg(v___x_4788_, v___y_4779_);
lean_dec_ref(v___y_4779_);
v___x_4790_ = 0;
v___x_4791_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4791_, 0, v___x_4774_);
lean_ctor_set_uint8(v___x_4791_, 1, v___x_4790_);
lean_ctor_set_uint8(v___x_4791_, 2, v___x_4790_);
lean_ctor_set_uint8(v___x_4791_, 3, v___x_4790_);
v___x_4792_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4789_, v___x_4791_);
v___x_4793_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*1, v___x_4774_);
v___x_4794_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4794_, 0, v_a_4782_);
lean_ctor_set_uint8(v___x_4794_, sizeof(void*)*1, v___x_4774_);
v___x_4795_ = lean_unsigned_to_nat(2u);
v___x_4796_ = lean_mk_empty_array_with_capacity(v___x_4795_);
v___x_4797_ = lean_array_push(v___x_4796_, v___x_4793_);
v___x_4798_ = lean_array_push(v___x_4797_, v___x_4794_);
v___x_4799_ = l_Lean_Fmt_Layouts_blocks(v___x_4798_, v___x_4774_);
lean_dec_ref(v___x_4798_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v___x_4799_);
v___x_4801_ = v___x_4785_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4802_, 1, v_a_4783_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
else
{
lean_dec_ref(v___y_4779_);
lean_dec_ref(v___y_4776_);
return v___x_4781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvNormalize___boxed(lean_object* v_x_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Lean_Fmt_fmtGrindBvNormalize(v_x_4865_, v_a_4866_, v_a_4867_);
lean_dec_ref(v_a_4866_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1(){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4875_ = l_Lean_Fmt_fmtAttribute;
v___x_4876_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__1));
v___x_4877_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___closed__1));
v___x_4878_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindBvNormalize___boxed), 3, 0);
v___x_4879_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4875_, v___x_4876_, v___x_4877_, v___x_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1___boxed(lean_object* v_a_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1();
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvDecide(lean_object* v_x_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v___x_4892_; uint8_t v___x_4893_; 
v___x_4892_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvDecide___closed__1));
lean_inc(v_x_4889_);
v___x_4893_ = l_Lean_Syntax_isOfKind(v_x_4889_, v___x_4892_);
if (v___x_4893_ == 0)
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
lean_dec(v_x_4889_);
v___x_4894_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4894_);
lean_ctor_set(v___x_4895_, 1, v_a_4891_);
return v___x_4895_;
}
else
{
lean_object* v___x_4896_; lean_object* v_cfg_4897_; lean_object* v___x_4898_; uint8_t v___x_4899_; lean_object* v___y_4901_; lean_object* v___y_4902_; lean_object* v___y_4903_; lean_object* v___y_4904_; lean_object* v___y_4905_; 
v___x_4896_ = lean_unsigned_to_nat(1u);
v_cfg_4897_ = l_Lean_Syntax_getArg(v_x_4889_, v___x_4896_);
v___x_4898_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__3));
lean_inc(v_cfg_4897_);
v___x_4899_ = l_Lean_Syntax_isOfKind(v_cfg_4897_, v___x_4898_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
lean_dec(v_cfg_4897_);
lean_dec(v_x_4889_);
v___x_4929_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4929_);
lean_ctor_set(v___x_4930_, 1, v_a_4891_);
return v___x_4930_;
}
else
{
lean_object* v___x_4931_; lean_object* v_bvDecideTk_4932_; lean_object* v_types_x3f_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___x_4977_; lean_object* v___x_4978_; uint8_t v___x_4979_; 
v___x_4931_ = lean_unsigned_to_nat(0u);
v_bvDecideTk_4932_ = l_Lean_Syntax_getArg(v_x_4889_, v___x_4931_);
v___x_4977_ = lean_unsigned_to_nat(2u);
v___x_4978_ = l_Lean_Syntax_getArg(v_x_4889_, v___x_4977_);
lean_dec(v_x_4889_);
v___x_4979_ = l_Lean_Syntax_isNone(v___x_4978_);
if (v___x_4979_ == 0)
{
uint8_t v___x_4980_; 
lean_inc(v___x_4978_);
v___x_4980_ = l_Lean_Syntax_matchesNull(v___x_4978_, v___x_4896_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
lean_dec(v___x_4978_);
lean_dec(v_bvDecideTk_4932_);
lean_dec(v_cfg_4897_);
v___x_4981_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4981_);
lean_ctor_set(v___x_4982_, 1, v_a_4891_);
return v___x_4982_;
}
else
{
lean_object* v_types_x3f_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
v_types_x3f_4983_ = l_Lean_Syntax_getArg(v___x_4978_, v___x_4931_);
lean_dec(v___x_4978_);
v___x_4984_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__5));
lean_inc(v_types_x3f_4983_);
v___x_4985_ = l_Lean_Syntax_isOfKind(v_types_x3f_4983_, v___x_4984_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
lean_dec(v_types_x3f_4983_);
lean_dec(v_bvDecideTk_4932_);
lean_dec(v_cfg_4897_);
v___x_4986_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
lean_ctor_set(v___x_4987_, 1, v_a_4891_);
return v___x_4987_;
}
else
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4988_, 0, v_types_x3f_4983_);
v_types_x3f_4934_ = v___x_4988_;
v___y_4935_ = v_a_4890_;
v___y_4936_ = v_a_4891_;
goto v___jp_4933_;
}
}
}
else
{
lean_object* v___x_4989_; 
lean_dec(v___x_4978_);
v___x_4989_ = lean_box(0);
v_types_x3f_4934_ = v___x_4989_;
v___y_4935_ = v_a_4890_;
v___y_4936_ = v_a_4891_;
goto v___jp_4933_;
}
v___jp_4933_:
{
lean_object* v___x_4937_; 
v___x_4937_ = l_Lean_Fmt_fmt(v_bvDecideTk_4932_, v___y_4935_, v___y_4936_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v_a_4938_; lean_object* v_a_4939_; lean_object* v___x_4940_; 
v_a_4938_ = lean_ctor_get(v___x_4937_, 0);
lean_inc(v_a_4938_);
v_a_4939_ = lean_ctor_get(v___x_4937_, 1);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4937_, 2);
v___x_4940_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_4897_, v_a_4939_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v_a_4941_; lean_object* v_a_4942_; size_t v_sz_4943_; size_t v___x_4944_; lean_object* v___x_4945_; 
v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
lean_inc(v_a_4941_);
v_a_4942_ = lean_ctor_get(v___x_4940_, 1);
lean_inc(v_a_4942_);
lean_dec_ref_known(v___x_4940_, 2);
v_sz_4943_ = lean_array_size(v_a_4941_);
v___x_4944_ = ((size_t)0ULL);
v___x_4945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0(v_sz_4943_, v___x_4944_, v_a_4941_, v___y_4935_, v_a_4942_);
if (lean_obj_tag(v___x_4945_) == 0)
{
if (lean_obj_tag(v_types_x3f_4934_) == 0)
{
lean_object* v_a_4946_; lean_object* v_a_4947_; lean_object* v___x_4948_; 
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_a_4946_);
v_a_4947_ = lean_ctor_get(v___x_4945_, 1);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4945_, 2);
v___x_4948_ = lean_box(0);
v___y_4901_ = v_a_4947_;
v___y_4902_ = v_a_4938_;
v___y_4903_ = v_a_4946_;
v___y_4904_ = v___y_4935_;
v___y_4905_ = v___x_4948_;
goto v___jp_4900_;
}
else
{
lean_object* v_a_4949_; lean_object* v_a_4950_; lean_object* v_val_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4958_; 
v_a_4949_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_a_4949_);
v_a_4950_ = lean_ctor_get(v___x_4945_, 1);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___x_4945_, 2);
v_val_4951_ = lean_ctor_get(v_types_x3f_4934_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v_types_x3f_4934_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4953_ = v_types_x3f_4934_;
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_val_4951_);
lean_dec(v_types_x3f_4934_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v___x_4956_; 
if (v_isShared_4954_ == 0)
{
v___x_4956_ = v___x_4953_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_val_4951_);
v___x_4956_ = v_reuseFailAlloc_4957_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
v___y_4901_ = v_a_4950_;
v___y_4902_ = v_a_4938_;
v___y_4903_ = v_a_4949_;
v___y_4904_ = v___y_4935_;
v___y_4905_ = v___x_4956_;
goto v___jp_4900_;
}
}
}
}
else
{
lean_object* v_a_4959_; lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
lean_dec(v_a_4938_);
lean_dec(v_types_x3f_4934_);
v_a_4959_ = lean_ctor_get(v___x_4945_, 0);
v_a_4960_ = lean_ctor_get(v___x_4945_, 1);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4945_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_inc(v_a_4959_);
lean_dec(v___x_4945_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
if (v_isShared_4963_ == 0)
{
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4959_);
lean_ctor_set(v_reuseFailAlloc_4966_, 1, v_a_4960_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
else
{
lean_object* v_a_4968_; lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec(v_a_4938_);
lean_dec(v_types_x3f_4934_);
v_a_4968_ = lean_ctor_get(v___x_4940_, 0);
v_a_4969_ = lean_ctor_get(v___x_4940_, 1);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4940_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_inc(v_a_4968_);
lean_dec(v___x_4940_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4968_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
else
{
lean_dec(v_types_x3f_4934_);
lean_dec(v_cfg_4897_);
return v___x_4937_;
}
}
}
v___jp_4900_:
{
lean_object* v___x_4906_; 
v___x_4906_ = l_Lean_Fmt_fmt_x3f(v___y_4905_, v___y_4904_, v___y_4901_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4928_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
v_a_4908_ = lean_ctor_get(v___x_4906_, 1);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4910_ = v___x_4906_;
v_isShared_4911_ = v_isSharedCheck_4928_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_inc(v_a_4907_);
lean_dec(v___x_4906_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4928_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; uint8_t v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4926_; 
v___x_4912_ = lean_mk_empty_array_with_capacity(v___x_4896_);
v___x_4913_ = lean_array_push(v___x_4912_, v___y_4902_);
v___x_4914_ = l_Array_append___redArg(v___x_4913_, v___y_4903_);
lean_dec_ref(v___y_4903_);
v___x_4915_ = 0;
v___x_4916_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4916_, 0, v___x_4899_);
lean_ctor_set_uint8(v___x_4916_, 1, v___x_4915_);
lean_ctor_set_uint8(v___x_4916_, 2, v___x_4915_);
lean_ctor_set_uint8(v___x_4916_, 3, v___x_4915_);
v___x_4917_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4914_, v___x_4916_);
v___x_4918_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
lean_ctor_set_uint8(v___x_4918_, sizeof(void*)*1, v___x_4899_);
v___x_4919_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4919_, 0, v_a_4907_);
lean_ctor_set_uint8(v___x_4919_, sizeof(void*)*1, v___x_4899_);
v___x_4920_ = lean_unsigned_to_nat(2u);
v___x_4921_ = lean_mk_empty_array_with_capacity(v___x_4920_);
v___x_4922_ = lean_array_push(v___x_4921_, v___x_4918_);
v___x_4923_ = lean_array_push(v___x_4922_, v___x_4919_);
v___x_4924_ = l_Lean_Fmt_Layouts_blocks(v___x_4923_, v___x_4899_);
lean_dec_ref(v___x_4923_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 0, v___x_4924_);
v___x_4926_ = v___x_4910_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4924_);
lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_a_4908_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
else
{
lean_dec_ref(v___y_4903_);
lean_dec_ref(v___y_4902_);
return v___x_4906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvDecide___boxed(lean_object* v_x_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_Fmt_fmtGrindBvDecide(v_x_4990_, v_a_4991_, v_a_4992_);
lean_dec_ref(v_a_4991_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1(){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5000_ = l_Lean_Fmt_fmtAttribute;
v___x_5001_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvDecide___closed__1));
v___x_5002_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___closed__1));
v___x_5003_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindBvDecide___boxed), 3, 0);
v___x_5004_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5000_, v___x_5001_, v___x_5002_, v___x_5003_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1___boxed(lean_object* v_a_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1();
return v_res_5006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvTrace(lean_object* v_x_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
lean_object* v___x_5017_; uint8_t v___x_5018_; 
v___x_5017_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvTrace___closed__1));
lean_inc(v_x_5014_);
v___x_5018_ = l_Lean_Syntax_isOfKind(v_x_5014_, v___x_5017_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; lean_object* v___x_5020_; 
lean_dec(v_x_5014_);
v___x_5019_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
lean_ctor_set(v___x_5020_, 1, v_a_5016_);
return v___x_5020_;
}
else
{
lean_object* v___x_5021_; lean_object* v_cfg_5022_; lean_object* v___x_5023_; uint8_t v___x_5024_; lean_object* v___y_5026_; lean_object* v___y_5027_; lean_object* v___y_5028_; lean_object* v___y_5029_; lean_object* v___y_5030_; 
v___x_5021_ = lean_unsigned_to_nat(1u);
v_cfg_5022_ = l_Lean_Syntax_getArg(v_x_5014_, v___x_5021_);
v___x_5023_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__3));
lean_inc(v_cfg_5022_);
v___x_5024_ = l_Lean_Syntax_isOfKind(v_cfg_5022_, v___x_5023_);
if (v___x_5024_ == 0)
{
lean_object* v___x_5054_; lean_object* v___x_5055_; 
lean_dec(v_cfg_5022_);
lean_dec(v_x_5014_);
v___x_5054_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5054_);
lean_ctor_set(v___x_5055_, 1, v_a_5016_);
return v___x_5055_;
}
else
{
lean_object* v___x_5056_; lean_object* v_bvTraceTk_5057_; lean_object* v_types_x3f_5059_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v___x_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
v___x_5056_ = lean_unsigned_to_nat(0u);
v_bvTraceTk_5057_ = l_Lean_Syntax_getArg(v_x_5014_, v___x_5056_);
v___x_5102_ = lean_unsigned_to_nat(2u);
v___x_5103_ = l_Lean_Syntax_getArg(v_x_5014_, v___x_5102_);
lean_dec(v_x_5014_);
v___x_5104_ = l_Lean_Syntax_isNone(v___x_5103_);
if (v___x_5104_ == 0)
{
uint8_t v___x_5105_; 
lean_inc(v___x_5103_);
v___x_5105_ = l_Lean_Syntax_matchesNull(v___x_5103_, v___x_5021_);
if (v___x_5105_ == 0)
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
lean_dec(v___x_5103_);
lean_dec(v_bvTraceTk_5057_);
lean_dec(v_cfg_5022_);
v___x_5106_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
lean_ctor_set(v___x_5107_, 1, v_a_5016_);
return v___x_5107_;
}
else
{
lean_object* v_types_x3f_5108_; lean_object* v___x_5109_; uint8_t v___x_5110_; 
v_types_x3f_5108_ = l_Lean_Syntax_getArg(v___x_5103_, v___x_5056_);
lean_dec(v___x_5103_);
v___x_5109_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__5));
lean_inc(v_types_x3f_5108_);
v___x_5110_ = l_Lean_Syntax_isOfKind(v_types_x3f_5108_, v___x_5109_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; lean_object* v___x_5112_; 
lean_dec(v_types_x3f_5108_);
lean_dec(v_bvTraceTk_5057_);
lean_dec(v_cfg_5022_);
v___x_5111_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5112_, 0, v___x_5111_);
lean_ctor_set(v___x_5112_, 1, v_a_5016_);
return v___x_5112_;
}
else
{
lean_object* v___x_5113_; 
v___x_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5113_, 0, v_types_x3f_5108_);
v_types_x3f_5059_ = v___x_5113_;
v___y_5060_ = v_a_5015_;
v___y_5061_ = v_a_5016_;
goto v___jp_5058_;
}
}
}
else
{
lean_object* v___x_5114_; 
lean_dec(v___x_5103_);
v___x_5114_ = lean_box(0);
v_types_x3f_5059_ = v___x_5114_;
v___y_5060_ = v_a_5015_;
v___y_5061_ = v_a_5016_;
goto v___jp_5058_;
}
v___jp_5058_:
{
lean_object* v___x_5062_; 
v___x_5062_ = l_Lean_Fmt_fmt(v_bvTraceTk_5057_, v___y_5060_, v___y_5061_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v_a_5064_; lean_object* v___x_5065_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
v_a_5064_ = lean_ctor_get(v___x_5062_, 1);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5062_, 2);
v___x_5065_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_5022_, v_a_5064_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; lean_object* v_a_5067_; size_t v_sz_5068_; size_t v___x_5069_; lean_object* v___x_5070_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
v_a_5067_ = lean_ctor_get(v___x_5065_, 1);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5065_, 2);
v_sz_5068_ = lean_array_size(v_a_5066_);
v___x_5069_ = ((size_t)0ULL);
v___x_5070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0(v_sz_5068_, v___x_5069_, v_a_5066_, v___y_5060_, v_a_5067_);
if (lean_obj_tag(v___x_5070_) == 0)
{
if (lean_obj_tag(v_types_x3f_5059_) == 0)
{
lean_object* v_a_5071_; lean_object* v_a_5072_; lean_object* v___x_5073_; 
v_a_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc(v_a_5071_);
v_a_5072_ = lean_ctor_get(v___x_5070_, 1);
lean_inc(v_a_5072_);
lean_dec_ref_known(v___x_5070_, 2);
v___x_5073_ = lean_box(0);
v___y_5026_ = v_a_5072_;
v___y_5027_ = v_a_5071_;
v___y_5028_ = v___y_5060_;
v___y_5029_ = v_a_5063_;
v___y_5030_ = v___x_5073_;
goto v___jp_5025_;
}
else
{
lean_object* v_a_5074_; lean_object* v_a_5075_; lean_object* v_val_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
v_a_5074_ = lean_ctor_get(v___x_5070_, 0);
lean_inc(v_a_5074_);
v_a_5075_ = lean_ctor_get(v___x_5070_, 1);
lean_inc(v_a_5075_);
lean_dec_ref_known(v___x_5070_, 2);
v_val_5076_ = lean_ctor_get(v_types_x3f_5059_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v_types_x3f_5059_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v_types_x3f_5059_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_val_5076_);
lean_dec(v_types_x3f_5059_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_val_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
v___y_5026_ = v_a_5075_;
v___y_5027_ = v_a_5074_;
v___y_5028_ = v___y_5060_;
v___y_5029_ = v_a_5063_;
v___y_5030_ = v___x_5081_;
goto v___jp_5025_;
}
}
}
}
else
{
lean_object* v_a_5084_; lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec(v_a_5063_);
lean_dec(v_types_x3f_5059_);
v_a_5084_ = lean_ctor_get(v___x_5070_, 0);
v_a_5085_ = lean_ctor_get(v___x_5070_, 1);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5070_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_inc(v_a_5084_);
lean_dec(v___x_5070_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5084_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
else
{
lean_object* v_a_5093_; lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec(v_a_5063_);
lean_dec(v_types_x3f_5059_);
v_a_5093_ = lean_ctor_get(v___x_5065_, 0);
v_a_5094_ = lean_ctor_get(v___x_5065_, 1);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5065_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_inc(v_a_5093_);
lean_dec(v___x_5065_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5093_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
else
{
lean_dec(v_types_x3f_5059_);
lean_dec(v_cfg_5022_);
return v___x_5062_;
}
}
}
v___jp_5025_:
{
lean_object* v___x_5031_; 
v___x_5031_ = l_Lean_Fmt_fmt_x3f(v___y_5030_, v___y_5028_, v___y_5026_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5053_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
v_a_5033_ = lean_ctor_get(v___x_5031_, 1);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5035_ = v___x_5031_;
v_isShared_5036_ = v_isSharedCheck_5053_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_inc(v_a_5032_);
lean_dec(v___x_5031_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5053_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5051_; 
v___x_5037_ = lean_mk_empty_array_with_capacity(v___x_5021_);
v___x_5038_ = lean_array_push(v___x_5037_, v___y_5029_);
v___x_5039_ = l_Array_append___redArg(v___x_5038_, v___y_5027_);
lean_dec_ref(v___y_5027_);
v___x_5040_ = 0;
v___x_5041_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_5041_, 0, v___x_5024_);
lean_ctor_set_uint8(v___x_5041_, 1, v___x_5040_);
lean_ctor_set_uint8(v___x_5041_, 2, v___x_5040_);
lean_ctor_set_uint8(v___x_5041_, 3, v___x_5040_);
v___x_5042_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_5039_, v___x_5041_);
v___x_5043_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5043_, 0, v___x_5042_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*1, v___x_5024_);
v___x_5044_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5044_, 0, v_a_5032_);
lean_ctor_set_uint8(v___x_5044_, sizeof(void*)*1, v___x_5024_);
v___x_5045_ = lean_unsigned_to_nat(2u);
v___x_5046_ = lean_mk_empty_array_with_capacity(v___x_5045_);
v___x_5047_ = lean_array_push(v___x_5046_, v___x_5043_);
v___x_5048_ = lean_array_push(v___x_5047_, v___x_5044_);
v___x_5049_ = l_Lean_Fmt_Layouts_blocks(v___x_5048_, v___x_5024_);
lean_dec_ref(v___x_5048_);
if (v_isShared_5036_ == 0)
{
lean_ctor_set(v___x_5035_, 0, v___x_5049_);
v___x_5051_ = v___x_5035_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5049_);
lean_ctor_set(v_reuseFailAlloc_5052_, 1, v_a_5033_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
}
else
{
lean_dec_ref(v___y_5029_);
lean_dec_ref(v___y_5027_);
return v___x_5031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvTrace___boxed(lean_object* v_x_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Lean_Fmt_fmtGrindBvTrace(v_x_5115_, v_a_5116_, v_a_5117_);
lean_dec_ref(v_a_5116_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1(){
_start:
{
lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5125_ = l_Lean_Fmt_fmtAttribute;
v___x_5126_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvTrace___closed__1));
v___x_5127_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___closed__1));
v___x_5128_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindBvTrace___boxed), 3, 0);
v___x_5129_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5125_, v___x_5126_, v___x_5127_, v___x_5128_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1___boxed(lean_object* v_a_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1();
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvCheck(lean_object* v_x_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_){
_start:
{
lean_object* v___x_5142_; uint8_t v___x_5143_; 
v___x_5142_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvCheck___closed__1));
lean_inc(v_x_5139_);
v___x_5143_ = l_Lean_Syntax_isOfKind(v_x_5139_, v___x_5142_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; lean_object* v___x_5145_; 
lean_dec(v_x_5139_);
v___x_5144_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5144_);
lean_ctor_set(v___x_5145_, 1, v_a_5141_);
return v___x_5145_;
}
else
{
lean_object* v___x_5146_; lean_object* v_cfg_5147_; lean_object* v___x_5148_; uint8_t v___x_5149_; lean_object* v___y_5151_; lean_object* v___y_5152_; lean_object* v___y_5153_; lean_object* v___y_5154_; lean_object* v___y_5155_; lean_object* v___y_5156_; lean_object* v___y_5157_; 
v___x_5146_ = lean_unsigned_to_nat(1u);
v_cfg_5147_ = l_Lean_Syntax_getArg(v_x_5139_, v___x_5146_);
v___x_5148_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__3));
lean_inc(v_cfg_5147_);
v___x_5149_ = l_Lean_Syntax_isOfKind(v_cfg_5147_, v___x_5148_);
if (v___x_5149_ == 0)
{
lean_object* v___x_5185_; lean_object* v___x_5186_; 
lean_dec(v_cfg_5147_);
lean_dec(v_x_5139_);
v___x_5185_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5185_);
lean_ctor_set(v___x_5186_, 1, v_a_5141_);
return v___x_5186_;
}
else
{
lean_object* v___x_5187_; lean_object* v_bvCheckTk_5188_; lean_object* v_types_x3f_5190_; lean_object* v___y_5191_; lean_object* v___y_5192_; lean_object* v___x_5239_; lean_object* v___x_5240_; uint8_t v___x_5241_; 
v___x_5187_ = lean_unsigned_to_nat(0u);
v_bvCheckTk_5188_ = l_Lean_Syntax_getArg(v_x_5139_, v___x_5187_);
v___x_5239_ = lean_unsigned_to_nat(2u);
v___x_5240_ = l_Lean_Syntax_getArg(v_x_5139_, v___x_5239_);
v___x_5241_ = l_Lean_Syntax_isNone(v___x_5240_);
if (v___x_5241_ == 0)
{
uint8_t v___x_5242_; 
lean_inc(v___x_5240_);
v___x_5242_ = l_Lean_Syntax_matchesNull(v___x_5240_, v___x_5146_);
if (v___x_5242_ == 0)
{
lean_object* v___x_5243_; lean_object* v___x_5244_; 
lean_dec(v___x_5240_);
lean_dec(v_bvCheckTk_5188_);
lean_dec(v_cfg_5147_);
lean_dec(v_x_5139_);
v___x_5243_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5244_, 0, v___x_5243_);
lean_ctor_set(v___x_5244_, 1, v_a_5141_);
return v___x_5244_;
}
else
{
lean_object* v_types_x3f_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; 
v_types_x3f_5245_ = l_Lean_Syntax_getArg(v___x_5240_, v___x_5187_);
lean_dec(v___x_5240_);
v___x_5246_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__5));
lean_inc(v_types_x3f_5245_);
v___x_5247_ = l_Lean_Syntax_isOfKind(v_types_x3f_5245_, v___x_5246_);
if (v___x_5247_ == 0)
{
lean_object* v___x_5248_; lean_object* v___x_5249_; 
lean_dec(v_types_x3f_5245_);
lean_dec(v_bvCheckTk_5188_);
lean_dec(v_cfg_5147_);
lean_dec(v_x_5139_);
v___x_5248_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5249_, 0, v___x_5248_);
lean_ctor_set(v___x_5249_, 1, v_a_5141_);
return v___x_5249_;
}
else
{
lean_object* v___x_5250_; 
v___x_5250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5250_, 0, v_types_x3f_5245_);
v_types_x3f_5190_ = v___x_5250_;
v___y_5191_ = v_a_5140_;
v___y_5192_ = v_a_5141_;
goto v___jp_5189_;
}
}
}
else
{
lean_object* v___x_5251_; 
lean_dec(v___x_5240_);
v___x_5251_ = lean_box(0);
v_types_x3f_5190_ = v___x_5251_;
v___y_5191_ = v_a_5140_;
v___y_5192_ = v_a_5141_;
goto v___jp_5189_;
}
v___jp_5189_:
{
lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; uint8_t v___x_5196_; 
v___x_5193_ = lean_unsigned_to_nat(3u);
v___x_5194_ = l_Lean_Syntax_getArg(v_x_5139_, v___x_5193_);
lean_dec(v_x_5139_);
v___x_5195_ = ((lean_object*)(l_Lean_Fmt_fmtGrindFail___closed__3));
lean_inc(v___x_5194_);
v___x_5196_ = l_Lean_Syntax_isOfKind(v___x_5194_, v___x_5195_);
if (v___x_5196_ == 0)
{
lean_object* v___x_5197_; lean_object* v___x_5198_; 
lean_dec(v___x_5194_);
lean_dec(v_types_x3f_5190_);
lean_dec(v_bvCheckTk_5188_);
lean_dec(v_cfg_5147_);
v___x_5197_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
lean_ctor_set(v___x_5198_, 1, v___y_5192_);
return v___x_5198_;
}
else
{
lean_object* v___x_5199_; 
v___x_5199_ = l_Lean_Fmt_fmt(v_bvCheckTk_5188_, v___y_5191_, v___y_5192_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v_a_5201_; lean_object* v___x_5202_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5200_);
v_a_5201_ = lean_ctor_get(v___x_5199_, 1);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5199_, 2);
v___x_5202_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_5147_, v_a_5201_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v_a_5203_; lean_object* v_a_5204_; size_t v_sz_5205_; size_t v___x_5206_; lean_object* v___x_5207_; 
v_a_5203_ = lean_ctor_get(v___x_5202_, 0);
lean_inc(v_a_5203_);
v_a_5204_ = lean_ctor_get(v___x_5202_, 1);
lean_inc(v_a_5204_);
lean_dec_ref_known(v___x_5202_, 2);
v_sz_5205_ = lean_array_size(v_a_5203_);
v___x_5206_ = ((size_t)0ULL);
v___x_5207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0(v_sz_5205_, v___x_5206_, v_a_5203_, v___y_5191_, v_a_5204_);
if (lean_obj_tag(v___x_5207_) == 0)
{
if (lean_obj_tag(v_types_x3f_5190_) == 0)
{
lean_object* v_a_5208_; lean_object* v_a_5209_; lean_object* v___x_5210_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
v_a_5209_ = lean_ctor_get(v___x_5207_, 1);
lean_inc(v_a_5209_);
lean_dec_ref_known(v___x_5207_, 2);
v___x_5210_ = lean_box(0);
v___y_5151_ = v_a_5200_;
v___y_5152_ = v_a_5208_;
v___y_5153_ = v___x_5193_;
v___y_5154_ = v___y_5191_;
v___y_5155_ = v___x_5194_;
v___y_5156_ = v_a_5209_;
v___y_5157_ = v___x_5210_;
goto v___jp_5150_;
}
else
{
lean_object* v_a_5211_; lean_object* v_a_5212_; lean_object* v_val_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
v_a_5211_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5211_);
v_a_5212_ = lean_ctor_get(v___x_5207_, 1);
lean_inc(v_a_5212_);
lean_dec_ref_known(v___x_5207_, 2);
v_val_5213_ = lean_ctor_get(v_types_x3f_5190_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v_types_x3f_5190_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v_types_x3f_5190_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_val_5213_);
lean_dec(v_types_x3f_5190_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_val_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
v___y_5151_ = v_a_5200_;
v___y_5152_ = v_a_5211_;
v___y_5153_ = v___x_5193_;
v___y_5154_ = v___y_5191_;
v___y_5155_ = v___x_5194_;
v___y_5156_ = v_a_5212_;
v___y_5157_ = v___x_5218_;
goto v___jp_5150_;
}
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
lean_dec(v_a_5200_);
lean_dec(v___x_5194_);
lean_dec(v_types_x3f_5190_);
v_a_5221_ = lean_ctor_get(v___x_5207_, 0);
v_a_5222_ = lean_ctor_get(v___x_5207_, 1);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v___x_5207_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_inc(v_a_5221_);
lean_dec(v___x_5207_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5225_ == 0)
{
v___x_5227_ = v___x_5224_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5221_);
lean_ctor_set(v_reuseFailAlloc_5228_, 1, v_a_5222_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
}
else
{
lean_object* v_a_5230_; lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5238_; 
lean_dec(v_a_5200_);
lean_dec(v___x_5194_);
lean_dec(v_types_x3f_5190_);
v_a_5230_ = lean_ctor_get(v___x_5202_, 0);
v_a_5231_ = lean_ctor_get(v___x_5202_, 1);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5202_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_inc(v_a_5230_);
lean_dec(v___x_5202_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_a_5230_);
lean_ctor_set(v_reuseFailAlloc_5237_, 1, v_a_5231_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
}
}
else
{
lean_dec(v___x_5194_);
lean_dec(v_types_x3f_5190_);
lean_dec(v_cfg_5147_);
return v___x_5199_;
}
}
}
}
v___jp_5150_:
{
lean_object* v___x_5158_; 
v___x_5158_ = l_Lean_Fmt_fmt_x3f(v___y_5157_, v___y_5154_, v___y_5156_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_object* v_a_5159_; lean_object* v_a_5160_; lean_object* v___x_5161_; 
v_a_5159_ = lean_ctor_get(v___x_5158_, 0);
lean_inc(v_a_5159_);
v_a_5160_ = lean_ctor_get(v___x_5158_, 1);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5158_, 2);
v___x_5161_ = l_Lean_Fmt_fmt(v___y_5155_, v___y_5154_, v_a_5160_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5184_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
v_a_5163_ = lean_ctor_get(v___x_5161_, 1);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5165_ = v___x_5161_;
v_isShared_5166_ = v_isSharedCheck_5184_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_inc(v_a_5162_);
lean_dec(v___x_5161_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5184_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5182_; 
v___x_5167_ = lean_mk_empty_array_with_capacity(v___x_5146_);
v___x_5168_ = lean_array_push(v___x_5167_, v___y_5151_);
v___x_5169_ = l_Array_append___redArg(v___x_5168_, v___y_5152_);
lean_dec_ref(v___y_5152_);
v___x_5170_ = 0;
v___x_5171_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_5171_, 0, v___x_5149_);
lean_ctor_set_uint8(v___x_5171_, 1, v___x_5170_);
lean_ctor_set_uint8(v___x_5171_, 2, v___x_5170_);
lean_ctor_set_uint8(v___x_5171_, 3, v___x_5170_);
v___x_5172_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_5169_, v___x_5171_);
v___x_5173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5173_, 0, v___x_5172_);
lean_ctor_set_uint8(v___x_5173_, sizeof(void*)*1, v___x_5149_);
v___x_5174_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5174_, 0, v_a_5159_);
lean_ctor_set_uint8(v___x_5174_, sizeof(void*)*1, v___x_5149_);
v___x_5175_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5175_, 0, v_a_5162_);
lean_ctor_set_uint8(v___x_5175_, sizeof(void*)*1, v___x_5149_);
v___x_5176_ = lean_mk_empty_array_with_capacity(v___y_5153_);
v___x_5177_ = lean_array_push(v___x_5176_, v___x_5173_);
v___x_5178_ = lean_array_push(v___x_5177_, v___x_5174_);
v___x_5179_ = lean_array_push(v___x_5178_, v___x_5175_);
v___x_5180_ = l_Lean_Fmt_Layouts_blocks(v___x_5179_, v___x_5149_);
lean_dec_ref(v___x_5179_);
if (v_isShared_5166_ == 0)
{
lean_ctor_set(v___x_5165_, 0, v___x_5180_);
v___x_5182_ = v___x_5165_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5180_);
lean_ctor_set(v_reuseFailAlloc_5183_, 1, v_a_5163_);
v___x_5182_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
return v___x_5182_;
}
}
}
else
{
lean_dec(v_a_5159_);
lean_dec_ref(v___y_5152_);
lean_dec_ref(v___y_5151_);
return v___x_5161_;
}
}
else
{
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5152_);
lean_dec_ref(v___y_5151_);
return v___x_5158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvCheck___boxed(lean_object* v_x_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l_Lean_Fmt_fmtGrindBvCheck(v_x_5252_, v_a_5253_, v_a_5254_);
lean_dec_ref(v_a_5253_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1(){
_start:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; 
v___x_5262_ = l_Lean_Fmt_fmtAttribute;
v___x_5263_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvCheck___closed__1));
v___x_5264_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___closed__1));
v___x_5265_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindBvCheck___boxed), 3, 0);
v___x_5266_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5262_, v___x_5263_, v___x_5264_, v___x_5265_);
return v___x_5266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1___boxed(lean_object* v_a_5267_){
_start:
{
lean_object* v_res_5268_; 
v_res_5268_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1();
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvDecidePush(lean_object* v_x_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_){
_start:
{
lean_object* v___x_5279_; uint8_t v___x_5280_; 
v___x_5279_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvDecidePush___closed__1));
lean_inc(v_x_5276_);
v___x_5280_ = l_Lean_Syntax_isOfKind(v_x_5276_, v___x_5279_);
if (v___x_5280_ == 0)
{
lean_object* v___x_5281_; lean_object* v___x_5282_; 
lean_dec(v_x_5276_);
v___x_5281_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5281_);
lean_ctor_set(v___x_5282_, 1, v_a_5278_);
return v___x_5282_;
}
else
{
lean_object* v___x_5283_; lean_object* v_cfg_5284_; lean_object* v___x_5285_; uint8_t v___x_5286_; 
v___x_5283_ = lean_unsigned_to_nat(1u);
v_cfg_5284_ = l_Lean_Syntax_getArg(v_x_5276_, v___x_5283_);
v___x_5285_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvNormalize___closed__3));
lean_inc(v_cfg_5284_);
v___x_5286_ = l_Lean_Syntax_isOfKind(v_cfg_5284_, v___x_5285_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
lean_dec(v_cfg_5284_);
lean_dec(v_x_5276_);
v___x_5287_ = l_Lean_Fmt_Error_partialFormatter;
v___x_5288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5288_, 0, v___x_5287_);
lean_ctor_set(v___x_5288_, 1, v_a_5278_);
return v___x_5288_;
}
else
{
lean_object* v___x_5289_; lean_object* v_bvDecidePushTk_5290_; lean_object* v___x_5291_; 
v___x_5289_ = lean_unsigned_to_nat(0u);
v_bvDecidePushTk_5290_ = l_Lean_Syntax_getArg(v_x_5276_, v___x_5289_);
lean_dec(v_x_5276_);
v___x_5291_ = l_Lean_Fmt_fmt(v_bvDecidePushTk_5290_, v_a_5277_, v_a_5278_);
if (lean_obj_tag(v___x_5291_) == 0)
{
lean_object* v_a_5292_; lean_object* v_a_5293_; lean_object* v___x_5294_; 
v_a_5292_ = lean_ctor_get(v___x_5291_, 0);
lean_inc(v_a_5292_);
v_a_5293_ = lean_ctor_get(v___x_5291_, 1);
lean_inc(v_a_5293_);
lean_dec_ref_known(v___x_5291_, 2);
v___x_5294_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_5284_, v_a_5293_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; lean_object* v_a_5296_; size_t v_sz_5297_; size_t v___x_5298_; lean_object* v___x_5299_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
v_a_5296_ = lean_ctor_get(v___x_5294_, 1);
lean_inc(v_a_5296_);
lean_dec_ref_known(v___x_5294_, 2);
v_sz_5297_ = lean_array_size(v_a_5295_);
v___x_5298_ = ((size_t)0ULL);
v___x_5299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtGrindBvNormalize_spec__0(v_sz_5297_, v___x_5298_, v_a_5295_, v_a_5277_, v_a_5296_);
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5314_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
v_a_5301_ = lean_ctor_get(v___x_5299_, 1);
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5314_ == 0)
{
v___x_5303_ = v___x_5299_;
v_isShared_5304_ = v_isSharedCheck_5314_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_inc(v_a_5300_);
lean_dec(v___x_5299_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5314_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; uint8_t v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5312_; 
v___x_5305_ = lean_mk_empty_array_with_capacity(v___x_5283_);
v___x_5306_ = lean_array_push(v___x_5305_, v_a_5292_);
v___x_5307_ = l_Array_append___redArg(v___x_5306_, v_a_5300_);
lean_dec(v_a_5300_);
v___x_5308_ = 0;
v___x_5309_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_5309_, 0, v___x_5286_);
lean_ctor_set_uint8(v___x_5309_, 1, v___x_5308_);
lean_ctor_set_uint8(v___x_5309_, 2, v___x_5308_);
lean_ctor_set_uint8(v___x_5309_, 3, v___x_5308_);
v___x_5310_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_5307_, v___x_5309_);
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 0, v___x_5310_);
v___x_5312_ = v___x_5303_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5313_; 
v_reuseFailAlloc_5313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5313_, 0, v___x_5310_);
lean_ctor_set(v_reuseFailAlloc_5313_, 1, v_a_5301_);
v___x_5312_ = v_reuseFailAlloc_5313_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
return v___x_5312_;
}
}
}
else
{
lean_object* v_a_5315_; lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
lean_dec(v_a_5292_);
v_a_5315_ = lean_ctor_get(v___x_5299_, 0);
v_a_5316_ = lean_ctor_get(v___x_5299_, 1);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5299_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_inc(v_a_5315_);
lean_dec(v___x_5299_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5315_);
lean_ctor_set(v_reuseFailAlloc_5322_, 1, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
else
{
lean_object* v_a_5324_; lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
lean_dec(v_a_5292_);
v_a_5324_ = lean_ctor_get(v___x_5294_, 0);
v_a_5325_ = lean_ctor_get(v___x_5294_, 1);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5294_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_inc(v_a_5324_);
lean_dec(v___x_5294_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5324_);
lean_ctor_set(v_reuseFailAlloc_5331_, 1, v_a_5325_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
else
{
lean_dec(v_cfg_5284_);
return v___x_5291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBvDecidePush___boxed(lean_object* v_x_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_Lean_Fmt_fmtGrindBvDecidePush(v_x_5333_, v_a_5334_, v_a_5335_);
lean_dec_ref(v_a_5334_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1(){
_start:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5343_ = l_Lean_Fmt_fmtAttribute;
v___x_5344_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBvDecidePush___closed__1));
v___x_5345_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___closed__1));
v___x_5346_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindBvDecidePush___boxed), 3, 0);
v___x_5347_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5343_, v___x_5344_, v___x_5345_, v___x_5346_);
return v___x_5347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1___boxed(lean_object* v_a_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1();
return v_res_5349_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnchor___regBuiltin_Lean_Fmt_fmtGrindAnchor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemma___regBuiltin_Lean_Fmt_fmtGrindLemma__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindLemmaMin___regBuiltin_Lean_Fmt_fmtGrindLemmaMin__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindErase___regBuiltin_Lean_Fmt_fmtGrindErase__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParam___regBuiltin_Lean_Fmt_fmtGrindParam__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThmNs___regBuiltin_Lean_Fmt_fmtGrindThmNs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindThm___regBuiltin_Lean_Fmt_fmtGrindThm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterIdent___regBuiltin_Lean_Fmt_fmtGrindFilterIdent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLt___regBuiltin_Lean_Fmt_fmtGrindFilterGenLt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenEq___regBuiltin_Lean_Fmt_fmtGrindFilterGenEq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenNe___regBuiltin_Lean_Fmt_fmtGrindFilterGenNe__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLe___regBuiltin_Lean_Fmt_fmtGrindFilterGenLe__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenLeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenLeAscii__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGt___regBuiltin_Lean_Fmt_fmtGrindFilterGenGt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGe___regBuiltin_Lean_Fmt_fmtGrindFilterGenGe__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterGenGeAscii___regBuiltin_Lean_Fmt_fmtGrindFilterGenGeAscii__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterParen___regBuiltin_Lean_Fmt_fmtGrindFilterParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterAnd___regBuiltin_Lean_Fmt_fmtGrindFilterAnd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterOr___regBuiltin_Lean_Fmt_fmtGrindFilterOr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilterNot___regBuiltin_Lean_Fmt_fmtGrindFilterNot__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFilter___regBuiltin_Lean_Fmt_fmtGrindFilter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchor___regBuiltin_Lean_Fmt_fmtGrindRefAnchor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefAnchordOrd___regBuiltin_Lean_Fmt_fmtGrindRefAnchordOrd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRefTerm___regBuiltin_Lean_Fmt_fmtGrindRefTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindStep___regBuiltin_Lean_Fmt_fmtGrindStep__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq1Indented___regBuiltin_Lean_Fmt_fmtGrindSeq1Indented__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqBracketed___regBuiltin_Lean_Fmt_fmtGrindSeqBracketed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeq___regBuiltin_Lean_Fmt_fmtGrindSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowAsserted___regBuiltin_Lean_Fmt_fmtGrindShowAsserted__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTrue___regBuiltin_Lean_Fmt_fmtGrindShowTrue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowFalse___regBuiltin_Lean_Fmt_fmtGrindShowFalse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowEqcs___regBuiltin_Lean_Fmt_fmtGrindShowEqcs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowCases___regBuiltin_Lean_Fmt_fmtGrindShowCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowState___regBuiltin_Lean_Fmt_fmtGrindShowState__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCasesTrace___regBuiltin_Lean_Fmt_fmtGrindCasesTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindShowTerm___regBuiltin_Lean_Fmt_fmtGrindShowTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTacticCases___regBuiltin_Lean_Fmt_fmtGrindTacticCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindWithAnnotateState___regBuiltin_Lean_Fmt_fmtGrindWithAnnotateState__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFail___regBuiltin_Lean_Fmt_fmtGrindFail__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRenameI___regBuiltin_Lean_Fmt_fmtGrindRenameI__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindApply___regBuiltin_Lean_Fmt_fmtGrindApply__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInternalize___regBuiltin_Lean_Fmt_fmtGrindInternalize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindExact___regBuiltin_Lean_Fmt_fmtGrindExact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindInstantiate___regBuiltin_Lean_Fmt_fmtGrindInstantiate__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindUse___regBuiltin_Lean_Fmt_fmtGrindUse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinish___regBuiltin_Lean_Fmt_fmtGrindFinish__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFinishTrace___regBuiltin_Lean_Fmt_fmtGrindFinishTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHave___regBuiltin_Lean_Fmt_fmtGrindHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindHaveSilent___regBuiltin_Lean_Fmt_fmtGrindHaveSilent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNestedTacticCore___regBuiltin_Lean_Fmt_fmtGrindNestedTacticCore__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAllGoals___regBuiltin_Lean_Fmt_fmtGrindAllGoals__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindCase___regBuiltin_Lean_Fmt_fmtGrindCase__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindAnyGoals___regBuiltin_Lean_Fmt_fmtGrindAnyGoals__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFocus___regBuiltin_Lean_Fmt_fmtGrindFocus__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFailIfSuccess___regBuiltin_Lean_Fmt_fmtGrindFailIfSuccess__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindTry___regBuiltin_Lean_Fmt_fmtGrindTry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRepeat___regBuiltin_Lean_Fmt_fmtGrindRepeat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindNext___regBuiltin_Lean_Fmt_fmtGrindNext__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDot___regBuiltin_Lean_Fmt_fmtGrindDot__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtGrindSeqFocus = _init_l_Lean_Fmt_fmtGrindSeqFocus();
lean_mark_persistent(l_Lean_Fmt_fmtGrindSeqFocus);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSeqFocus___regBuiltin_Lean_Fmt_fmtGrindSeqFocus__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindFirst___regBuiltin_Lean_Fmt_fmtGrindFirst__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindParen___regBuiltin_Lean_Fmt_fmtGrindParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetOption___regBuiltin_Lean_Fmt_fmtGrindSetOption__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSetConfig___regBuiltin_Lean_Fmt_fmtGrindSetConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntro___regBuiltin_Lean_Fmt_fmtGrindSymIntro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntroLight___regBuiltin_Lean_Fmt_fmtGrindSymIntroLight__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntros___regBuiltin_Lean_Fmt_fmtGrindSymIntros__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSymIntrosLight___regBuiltin_Lean_Fmt_fmtGrindSymIntrosLight__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindSimp___regBuiltin_Lean_Fmt_fmtGrindSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindDSimp___regBuiltin_Lean_Fmt_fmtGrindDSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindRw___regBuiltin_Lean_Fmt_fmtGrindRw__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvNormalize___regBuiltin_Lean_Fmt_fmtGrindBvNormalize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecide___regBuiltin_Lean_Fmt_fmtGrindBvDecide__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvTrace___regBuiltin_Lean_Fmt_fmtGrindBvTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvCheck___regBuiltin_Lean_Fmt_fmtGrindBvCheck__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Interactive_0__Lean_Fmt_fmtGrindBvDecidePush___regBuiltin_Lean_Fmt_fmtGrindBvDecidePush__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Interactive(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Attr(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Tactics(uint8_t builtin);
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin);
lean_object* initialize_Init_Grind_Attr(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Grind_Interactive(builtin);
}
#ifdef __cplusplus
}
#endif
