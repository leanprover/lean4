// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Meta.Tactic.Grind.Parser
// Imports: public import Lean.Fmt.Formatters.Lean.Parser.Term.Basic public import Lean.Fmt.FmtM.Basic meta import Lean.Meta.Tactic.Grind.Parser import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtGrindIdentCnstr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGrindIdentCnstr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindIdentCnstr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentCnstr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentCnstr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLtCnstr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLtCnstr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLtCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLtCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTermCnstr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTermCnstr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTermCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTermCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqCnstr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqCnstr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindIsValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtGrindIsValue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGrindIsValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtGrindIsValue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindIsValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtGrindIsValue___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindIsValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "GrindCnstr"};
static const lean_object* l_Lean_Fmt_fmtGrindIsValue___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtGrindIsValue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValue"};
static const lean_object* l_Lean_Fmt_fmtGrindIsValue___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsValue___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsValue___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsValue___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsValue___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(142, 127, 91, 31, 152, 192, 239, 0)}};
static const lean_object* l_Lean_Fmt_fmtGrindIsValue___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtGrindIsValue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtGrindIsValue___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsValue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtGrindIsValue___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsValue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGrindIsValue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 18, 138, 96, 161, 146, 172, 130)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindIsStrictValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isStrictValue"};
static const lean_object* l_Lean_Fmt_fmtGrindIsStrictValue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsStrictValue___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindIsStrictValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 167, 118, 192, 170, 54, 174, 22)}};
static const lean_object* l_Lean_Fmt_fmtGrindIsStrictValue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsStrictValue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsStrictValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsStrictValue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtGrindIsStrictValue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 184, 234, 112, 192, 165, 105, 106)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindNotValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notValue"};
static const lean_object* l_Lean_Fmt_fmtGrindNotValue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindNotValue___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotValue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotValue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotValue___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotValue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotValue___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotValue___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindNotValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 180, 19, 60, 251, 16, 248, 4)}};
static const lean_object* l_Lean_Fmt_fmtGrindNotValue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindNotValue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotValue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindNotValue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 20, 141, 85, 116, 116, 76, 141)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindNotStrictValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "notStrictValue"};
static const lean_object* l_Lean_Fmt_fmtGrindNotStrictValue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindNotStrictValue___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindNotStrictValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 251, 19, 154, 122, 46, 102, 83)}};
static const lean_object* l_Lean_Fmt_fmtGrindNotStrictValue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindNotStrictValue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotStrictValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotStrictValue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtGrindNotStrictValue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 180, 197, 154, 140, 8, 144, 73)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindIsGround___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isGround"};
static const lean_object* l_Lean_Fmt_fmtGrindIsGround___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsGround___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsGround___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsGround___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsGround___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsGround___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsGround___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsGround___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsGround___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindIsGround___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindIsGround___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindIsGround___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 99, 47, 57, 220, 158, 80, 177)}};
static const lean_object* l_Lean_Fmt_fmtGrindIsGround___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindIsGround___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsGround(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsGround___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindIsGround"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 43, 247, 243, 96, 98, 6, 78)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSizeLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sizeLt"};
static const lean_object* l_Lean_Fmt_fmtGrindSizeLt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSizeLt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSizeLt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSizeLt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSizeLt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSizeLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 251, 30, 194, 200, 196, 155, 146)}};
static const lean_object* l_Lean_Fmt_fmtGrindSizeLt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindSizeLt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtGrindSizeLt___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSizeLt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtGrindSizeLt___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindSizeLt___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSizeLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSizeLt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtGrindSizeLt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 129, 166, 205, 255, 166, 168, 167)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindDepthLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depthLt"};
static const lean_object* l_Lean_Fmt_fmtGrindDepthLt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindDepthLt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindDepthLt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDepthLt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDepthLt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDepthLt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDepthLt___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDepthLt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDepthLt___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDepthLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDepthLt___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindDepthLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 13, 145, 164, 157, 20, 85, 11)}};
static const lean_object* l_Lean_Fmt_fmtGrindDepthLt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindDepthLt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDepthLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDepthLt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGrindDepthLt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 185, 203, 168, 246, 29, 133, 102)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindGenLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "genLt"};
static const lean_object* l_Lean_Fmt_fmtGrindGenLt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindGenLt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindGenLt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindGenLt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindGenLt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindGenLt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindGenLt___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindGenLt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindGenLt___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindGenLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindGenLt___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindGenLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 6, 178, 35, 133, 139, 189, 47)}};
static const lean_object* l_Lean_Fmt_fmtGrindGenLt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindGenLt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindGenLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindGenLt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindGenLt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 147, 214, 222, 185, 104, 144, 88)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindMaxInsts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxInsts"};
static const lean_object* l_Lean_Fmt_fmtGrindMaxInsts___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindMaxInsts___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindMaxInsts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 108, 68, 184, 240, 212, 209, 21)}};
static const lean_object* l_Lean_Fmt_fmtGrindMaxInsts___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindMaxInsts___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindMaxInsts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindMaxInsts___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindMaxInsts"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 123, 59, 122, 166, 47, 35, 1)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindGuard___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "guard"};
static const lean_object* l_Lean_Fmt_fmtGrindGuard___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindGuard___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindGuard___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindGuard___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindGuard___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindGuard___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindGuard___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindGuard___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindGuard___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindGuard___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindGuard___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindGuard___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 187, 126, 138, 230, 109, 238, 75)}};
static const lean_object* l_Lean_Fmt_fmtGrindGuard___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindGuard___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindGuard(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindGuard___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindGuard"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 69, 88, 103, 71, 213, 192, 9)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l_Lean_Fmt_fmtGrindCheck___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindCheck___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindCheck___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCheck___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCheck___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCheck___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCheck___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCheck___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCheck___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCheck___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 211, 65, 46, 115, 168, 222, 235)}};
static const lean_object* l_Lean_Fmt_fmtGrindCheck___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindCheck___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCheck(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCheck___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindCheck"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 118, 97, 123, 232, 90, 80, 103)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindNotDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notDefEq"};
static const lean_object* l_Lean_Fmt_fmtGrindNotDefEq___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindNotDefEq___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindNotDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 71, 120, 134, 181, 74, 206, 169)}};
static const lean_object* l_Lean_Fmt_fmtGrindNotDefEq___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindNotDefEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotDefEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotDefEq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindNotDefEq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 166, 236, 90, 184, 175, 146, 0)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "defEq"};
static const lean_object* l_Lean_Fmt_fmtGrindDefEq___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindDefEq___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindDefEq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDefEq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDefEq___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDefEq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDefEq___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDefEq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDefEq___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(11, 28, 170, 8, 100, 241, 75, 105)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindDefEq___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 16, 176, 15, 194, 80, 158, 173)}};
static const lean_object* l_Lean_Fmt_fmtGrindDefEq___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindDefEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDefEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDefEq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindDefEq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 115, 245, 193, 23, 132, 28, 46)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindPattern"};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 150, 72, 45, 239, 118, 187, 30)}};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__4_value;
static const lean_array_object l_Lean_Fmt_fmtGrindPattern___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPattern___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPattern___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grindPatternCnstrs"};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPattern___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__7_value),LEAN_SCALAR_PTR_LITERAL(9, 242, 154, 125, 67, 48, 229, 39)}};
static const lean_object* l_Lean_Fmt_fmtGrindPattern___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtGrindPattern___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPattern___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGrindPattern"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 37, 232, 251, 53, 34, 172, 45)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtInitGrindNorm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "initGrindNorm"};
static const lean_object* l_Lean_Fmt_fmtInitGrindNorm___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtInitGrindNorm___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtInitGrindNorm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInitGrindNorm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInitGrindNorm___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtInitGrindNorm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInitGrindNorm___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtInitGrindNorm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInitGrindNorm___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtInitGrindNorm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 56, 244, 141, 180, 41, 47, 38)}};
static const lean_object* l_Lean_Fmt_fmtInitGrindNorm___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtInitGrindNorm___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInitGrindNorm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInitGrindNorm___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtInitGrindNorm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindIsValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 224, 238, 215, 174, 218, 21, 73)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentCnstr___redArg(lean_object* v_tk_4_, lean_object* v_id_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Fmt_fmt(v_tk_4_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_a_9_);
v_a_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_a_10_);
lean_dec_ref_known(v___x_8_, 2);
v___x_11_ = l_Lean_Fmt_fmt(v_id_5_, v_a_6_, v_a_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_26_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
v_a_13_ = lean_ctor_get(v___x_11_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_26_ == 0)
{
v___x_15_ = v___x_11_;
v_isShared_16_ = v_isSharedCheck_26_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_inc(v_a_12_);
lean_dec(v___x_11_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_26_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
v___x_19_ = lean_array_push(v___x_18_, v_a_9_);
v___x_20_ = lean_array_push(v___x_19_, v_a_12_);
v___x_21_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIdentCnstr___redArg___closed__0));
v___x_22_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_20_, v___x_21_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_22_);
v___x_24_ = v___x_15_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_a_13_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
else
{
lean_dec(v_a_9_);
return v___x_11_;
}
}
else
{
lean_dec(v_id_5_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentCnstr___redArg___boxed(lean_object* v_tk_27_, lean_object* v_id_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_tk_27_, v_id_28_, v_a_29_, v_a_30_);
lean_dec_ref(v_a_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentCnstr(lean_object* v_tk_32_, lean_object* v_id_33_, lean_object* v___semiTk_x3f_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_tk_32_, v_id_33_, v_a_35_, v_a_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentCnstr___boxed(lean_object* v_tk_38_, lean_object* v_id_39_, lean_object* v___semiTk_x3f_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Fmt_fmtGrindIdentCnstr(v_tk_38_, v_id_39_, v___semiTk_x3f_40_, v_a_41_, v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v___semiTk_x3f_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg(lean_object* v_tk_47_, lean_object* v_id_48_, lean_object* v_ltTk_49_, lean_object* v_n_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Fmt_fmt(v_tk_47_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v_a_55_; lean_object* v___x_56_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
v_a_55_ = lean_ctor_get(v___x_53_, 1);
lean_inc(v_a_55_);
lean_dec_ref_known(v___x_53_, 2);
v___x_56_ = l_Lean_Fmt_fmt(v_id_48_, v_a_51_, v_a_55_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v_a_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
v_a_58_ = lean_ctor_get(v___x_56_, 1);
lean_inc(v_a_58_);
lean_dec_ref_known(v___x_56_, 2);
v___x_59_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIdentCnstr___redArg___closed__0));
v___x_60_ = l_Lean_Fmt_fmt(v_ltTk_49_, v_a_51_, v_a_58_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___x_63_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
v_a_62_ = lean_ctor_get(v___x_60_, 1);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_60_, 2);
v___x_63_ = l_Lean_Fmt_fmt(v_n_50_, v_a_51_, v_a_62_);
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
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = lean_mk_empty_array_with_capacity(v___x_69_);
v___x_71_ = lean_array_push(v___x_70_, v_a_54_);
v___x_72_ = lean_array_push(v___x_71_, v_a_57_);
v___x_73_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_72_, v___x_59_);
v___x_74_ = lean_unsigned_to_nat(3u);
v___x_75_ = lean_mk_empty_array_with_capacity(v___x_74_);
v___x_76_ = lean_array_push(v___x_75_, v___x_73_);
v___x_77_ = lean_array_push(v___x_76_, v_a_61_);
v___x_78_ = lean_array_push(v___x_77_, v_a_64_);
v___x_79_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg___closed__0));
v___x_80_ = l_Lean_Fmt_Layouts_infixOperator(v___x_78_, v___x_79_);
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
lean_dec(v_a_61_);
lean_dec(v_a_57_);
lean_dec(v_a_54_);
return v___x_63_;
}
}
else
{
lean_dec(v_a_57_);
lean_dec(v_a_54_);
lean_dec(v_n_50_);
return v___x_60_;
}
}
else
{
lean_dec(v_a_54_);
lean_dec(v_n_50_);
lean_dec(v_ltTk_49_);
return v___x_56_;
}
}
else
{
lean_dec(v_n_50_);
lean_dec(v_ltTk_49_);
lean_dec(v_id_48_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg___boxed(lean_object* v_tk_85_, lean_object* v_id_86_, lean_object* v_ltTk_87_, lean_object* v_n_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg(v_tk_85_, v_id_86_, v_ltTk_87_, v_n_88_, v_a_89_, v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr(lean_object* v_tk_92_, lean_object* v_id_93_, lean_object* v_ltTk_94_, lean_object* v_n_95_, lean_object* v___semiTk_x3f_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg(v_tk_92_, v_id_93_, v_ltTk_94_, v_n_95_, v_a_97_, v_a_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIdentLtCnstr___boxed(lean_object* v_tk_100_, lean_object* v_id_101_, lean_object* v_ltTk_102_, lean_object* v_n_103_, lean_object* v___semiTk_x3f_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Fmt_fmtGrindIdentLtCnstr(v_tk_100_, v_id_101_, v_ltTk_102_, v_n_103_, v___semiTk_x3f_104_, v_a_105_, v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v___semiTk_x3f_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLtCnstr___redArg(lean_object* v_tk_108_, lean_object* v_ltTk_109_, lean_object* v_n_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Fmt_fmt(v_tk_108_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v_a_115_; lean_object* v___x_116_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
v_a_115_ = lean_ctor_get(v___x_113_, 1);
lean_inc(v_a_115_);
lean_dec_ref_known(v___x_113_, 2);
v___x_116_ = l_Lean_Fmt_fmt(v_ltTk_109_, v_a_111_, v_a_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v_a_118_; lean_object* v___x_119_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
v_a_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_116_, 2);
v___x_119_ = l_Lean_Fmt_fmt(v_n_110_, v_a_111_, v_a_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_135_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_a_121_ = lean_ctor_get(v___x_119_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_135_ == 0)
{
v___x_123_ = v___x_119_;
v_isShared_124_ = v_isSharedCheck_135_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_135_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_125_ = lean_unsigned_to_nat(3u);
v___x_126_ = lean_mk_empty_array_with_capacity(v___x_125_);
v___x_127_ = lean_array_push(v___x_126_, v_a_114_);
v___x_128_ = lean_array_push(v___x_127_, v_a_117_);
v___x_129_ = lean_array_push(v___x_128_, v_a_120_);
v___x_130_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg___closed__0));
v___x_131_ = l_Lean_Fmt_Layouts_infixOperator(v___x_129_, v___x_130_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_131_);
v___x_133_ = v___x_123_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_a_121_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
else
{
lean_dec(v_a_117_);
lean_dec(v_a_114_);
return v___x_119_;
}
}
else
{
lean_dec(v_a_114_);
lean_dec(v_n_110_);
return v___x_116_;
}
}
else
{
lean_dec(v_n_110_);
lean_dec(v_ltTk_109_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLtCnstr___redArg___boxed(lean_object* v_tk_136_, lean_object* v_ltTk_137_, lean_object* v_n_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Fmt_fmtGrindLtCnstr___redArg(v_tk_136_, v_ltTk_137_, v_n_138_, v_a_139_, v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLtCnstr(lean_object* v_tk_142_, lean_object* v_ltTk_143_, lean_object* v_n_144_, lean_object* v___semiTk_x3f_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Fmt_fmtGrindLtCnstr___redArg(v_tk_142_, v_ltTk_143_, v_n_144_, v_a_146_, v_a_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLtCnstr___boxed(lean_object* v_tk_149_, lean_object* v_ltTk_150_, lean_object* v_n_151_, lean_object* v___semiTk_x3f_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Fmt_fmtGrindLtCnstr(v_tk_149_, v_ltTk_150_, v_n_151_, v___semiTk_x3f_152_, v_a_153_, v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v___semiTk_x3f_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTermCnstr___redArg(lean_object* v_tk_156_, lean_object* v_t_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Fmt_fmt(v_tk_156_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v_a_162_; lean_object* v___x_163_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
v_a_162_ = lean_ctor_get(v___x_160_, 1);
lean_inc(v_a_162_);
lean_dec_ref_known(v___x_160_, 2);
v___x_163_ = l_Lean_Fmt_fmt(v_t_157_, v_a_158_, v_a_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_178_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_a_165_ = lean_ctor_get(v___x_163_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_178_ == 0)
{
v___x_167_ = v___x_163_;
v_isShared_168_ = v_isSharedCheck_178_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_178_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_169_ = lean_unsigned_to_nat(2u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_array_push(v___x_170_, v_a_161_);
v___x_172_ = lean_array_push(v___x_171_, v_a_164_);
v___x_173_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIdentCnstr___redArg___closed__0));
v___x_174_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_172_, v___x_173_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_174_);
v___x_176_ = v___x_167_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_a_165_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
lean_dec(v_a_161_);
return v___x_163_;
}
}
else
{
lean_dec(v_t_157_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTermCnstr___redArg___boxed(lean_object* v_tk_179_, lean_object* v_t_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Fmt_fmtGrindTermCnstr___redArg(v_tk_179_, v_t_180_, v_a_181_, v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTermCnstr(lean_object* v_tk_184_, lean_object* v_t_185_, lean_object* v___semiTk_x3f_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Fmt_fmtGrindTermCnstr___redArg(v_tk_184_, v_t_185_, v_a_187_, v_a_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTermCnstr___boxed(lean_object* v_tk_190_, lean_object* v_t_191_, lean_object* v___semiTk_x3f_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Fmt_fmtGrindTermCnstr(v_tk_190_, v_t_191_, v___semiTk_x3f_192_, v_a_193_, v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v___semiTk_x3f_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqCnstr___redArg(lean_object* v_id_196_, lean_object* v_eqTk_197_, lean_object* v_rhs_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Fmt_fmt(v_id_196_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v_a_203_; lean_object* v___x_204_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
v_a_203_ = lean_ctor_get(v___x_201_, 1);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_201_, 2);
v___x_204_ = l_Lean_Fmt_fmt(v_eqTk_197_, v_a_199_, v_a_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v_a_206_; lean_object* v___x_207_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
v_a_206_ = lean_ctor_get(v___x_204_, 1);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_204_, 2);
v___x_207_ = l_Lean_Fmt_fmt(v_rhs_198_, v_a_199_, v_a_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_223_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_a_209_ = lean_ctor_get(v___x_207_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_223_ == 0)
{
v___x_211_ = v___x_207_;
v_isShared_212_ = v_isSharedCheck_223_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_223_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_213_ = lean_unsigned_to_nat(3u);
v___x_214_ = lean_mk_empty_array_with_capacity(v___x_213_);
v___x_215_ = lean_array_push(v___x_214_, v_a_202_);
v___x_216_ = lean_array_push(v___x_215_, v_a_205_);
v___x_217_ = lean_array_push(v___x_216_, v_a_208_);
v___x_218_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg___closed__0));
v___x_219_ = l_Lean_Fmt_Layouts_infixOperator(v___x_217_, v___x_218_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_219_);
v___x_221_ = v___x_211_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_a_209_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_dec(v_a_205_);
lean_dec(v_a_202_);
return v___x_207_;
}
}
else
{
lean_dec(v_a_202_);
lean_dec(v_rhs_198_);
return v___x_204_;
}
}
else
{
lean_dec(v_rhs_198_);
lean_dec(v_eqTk_197_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqCnstr___redArg___boxed(lean_object* v_id_224_, lean_object* v_eqTk_225_, lean_object* v_rhs_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Fmt_fmtGrindEqCnstr___redArg(v_id_224_, v_eqTk_225_, v_rhs_226_, v_a_227_, v_a_228_);
lean_dec_ref(v_a_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqCnstr(lean_object* v_id_230_, lean_object* v_eqTk_231_, lean_object* v_rhs_232_, lean_object* v___semiTk_x3f_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Fmt_fmtGrindEqCnstr___redArg(v_id_230_, v_eqTk_231_, v_rhs_232_, v_a_234_, v_a_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqCnstr___boxed(lean_object* v_id_237_, lean_object* v_eqTk_238_, lean_object* v_rhs_239_, lean_object* v___semiTk_x3f_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Fmt_fmtGrindEqCnstr(v_id_237_, v_eqTk_238_, v_rhs_239_, v___semiTk_x3f_240_, v_a_241_, v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v___semiTk_x3f_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsValue(lean_object* v_x_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__5));
lean_inc(v_x_258_);
v___x_262_ = l_Lean_Syntax_isOfKind(v_x_258_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v_x_258_);
v___x_263_ = l_Lean_Fmt_Error_partialFormatter;
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_a_260_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v_id_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v_id_266_ = l_Lean_Syntax_getArg(v_x_258_, v___x_265_);
v___x_267_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_266_);
v___x_268_ = l_Lean_Syntax_isOfKind(v_id_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v_id_266_);
lean_dec(v_x_258_);
v___x_269_ = l_Lean_Fmt_Error_partialFormatter;
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_a_260_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v_isValueTk_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_271_ = lean_unsigned_to_nat(0u);
v_isValueTk_272_ = l_Lean_Syntax_getArg(v_x_258_, v___x_271_);
v___x_273_ = lean_unsigned_to_nat(2u);
v___x_274_ = l_Lean_Syntax_getArg(v_x_258_, v___x_273_);
lean_dec(v_x_258_);
v___x_275_ = l_Lean_Syntax_isNone(v___x_274_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
v___x_276_ = l_Lean_Syntax_matchesNull(v___x_274_, v___x_265_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_isValueTk_272_);
lean_dec(v_id_266_);
v___x_277_ = l_Lean_Fmt_Error_partialFormatter;
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_260_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_isValueTk_272_, v_id_266_, v_a_259_, v_a_260_);
return v___x_279_;
}
}
else
{
lean_object* v___x_280_; 
lean_dec(v___x_274_);
v___x_280_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_isValueTk_272_, v_id_266_, v_a_259_, v_a_260_);
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsValue___boxed(lean_object* v_x_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Fmt_fmtGrindIsValue(v_x_281_, v_a_282_, v_a_283_);
lean_dec_ref(v_a_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1(){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_292_ = l_Lean_Fmt_fmtAttribute;
v___x_293_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__5));
v___x_294_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___closed__2));
v___x_295_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindIsValue___boxed), 3, 0);
v___x_296_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_292_, v___x_293_, v___x_294_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1___boxed(lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1();
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsStrictValue(lean_object* v_x_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsStrictValue___closed__1));
lean_inc(v_x_306_);
v___x_310_ = l_Lean_Syntax_isOfKind(v_x_306_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_x_306_);
v___x_311_ = l_Lean_Fmt_Error_partialFormatter;
v___x_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_a_308_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v_id_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_313_ = lean_unsigned_to_nat(1u);
v_id_314_ = l_Lean_Syntax_getArg(v_x_306_, v___x_313_);
v___x_315_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_314_);
v___x_316_ = l_Lean_Syntax_isOfKind(v_id_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_id_314_);
lean_dec(v_x_306_);
v___x_317_ = l_Lean_Fmt_Error_partialFormatter;
v___x_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_a_308_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; lean_object* v_isStrictValueTk_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v_isStrictValueTk_320_ = l_Lean_Syntax_getArg(v_x_306_, v___x_319_);
v___x_321_ = lean_unsigned_to_nat(2u);
v___x_322_ = l_Lean_Syntax_getArg(v_x_306_, v___x_321_);
lean_dec(v_x_306_);
v___x_323_ = l_Lean_Syntax_isNone(v___x_322_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = l_Lean_Syntax_matchesNull(v___x_322_, v___x_313_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_isStrictValueTk_320_);
lean_dec(v_id_314_);
v___x_325_ = l_Lean_Fmt_Error_partialFormatter;
v___x_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v_a_308_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_isStrictValueTk_320_, v_id_314_, v_a_307_, v_a_308_);
return v___x_327_;
}
}
else
{
lean_object* v___x_328_; 
lean_dec(v___x_322_);
v___x_328_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_isStrictValueTk_320_, v_id_314_, v_a_307_, v_a_308_);
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsStrictValue___boxed(lean_object* v_x_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Fmt_fmtGrindIsStrictValue(v_x_329_, v_a_330_, v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1(){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_339_ = l_Lean_Fmt_fmtAttribute;
v___x_340_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsStrictValue___closed__1));
v___x_341_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___closed__1));
v___x_342_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindIsStrictValue___boxed), 3, 0);
v___x_343_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_339_, v___x_340_, v___x_341_, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1___boxed(lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1();
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotValue(lean_object* v_x_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNotValue___closed__1));
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
lean_object* v___x_360_; lean_object* v_id_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v_id_361_ = l_Lean_Syntax_getArg(v_x_353_, v___x_360_);
v___x_362_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_361_);
v___x_363_ = l_Lean_Syntax_isOfKind(v_id_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_id_361_);
lean_dec(v_x_353_);
v___x_364_ = l_Lean_Fmt_Error_partialFormatter;
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_a_355_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; lean_object* v_notValueTk_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v_notValueTk_367_ = l_Lean_Syntax_getArg(v_x_353_, v___x_366_);
v___x_368_ = lean_unsigned_to_nat(2u);
v___x_369_ = l_Lean_Syntax_getArg(v_x_353_, v___x_368_);
lean_dec(v_x_353_);
v___x_370_ = l_Lean_Syntax_isNone(v___x_369_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
v___x_371_ = l_Lean_Syntax_matchesNull(v___x_369_, v___x_360_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v_notValueTk_367_);
lean_dec(v_id_361_);
v___x_372_ = l_Lean_Fmt_Error_partialFormatter;
v___x_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_a_355_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_notValueTk_367_, v_id_361_, v_a_354_, v_a_355_);
return v___x_374_;
}
}
else
{
lean_object* v___x_375_; 
lean_dec(v___x_369_);
v___x_375_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_notValueTk_367_, v_id_361_, v_a_354_, v_a_355_);
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotValue___boxed(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Fmt_fmtGrindNotValue(v_x_376_, v_a_377_, v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1(){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_386_ = l_Lean_Fmt_fmtAttribute;
v___x_387_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNotValue___closed__1));
v___x_388_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___closed__1));
v___x_389_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindNotValue___boxed), 3, 0);
v___x_390_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_386_, v___x_387_, v___x_388_, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1___boxed(lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1();
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotStrictValue(lean_object* v_x_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNotStrictValue___closed__1));
lean_inc(v_x_400_);
v___x_404_ = l_Lean_Syntax_isOfKind(v_x_400_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_x_400_);
v___x_405_ = l_Lean_Fmt_Error_partialFormatter;
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_a_402_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v_id_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v_id_408_ = l_Lean_Syntax_getArg(v_x_400_, v___x_407_);
v___x_409_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_408_);
v___x_410_ = l_Lean_Syntax_isOfKind(v_id_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec(v_id_408_);
lean_dec(v_x_400_);
v___x_411_ = l_Lean_Fmt_Error_partialFormatter;
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_a_402_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; lean_object* v_notStrictValueTk_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v_notStrictValueTk_414_ = l_Lean_Syntax_getArg(v_x_400_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(2u);
v___x_416_ = l_Lean_Syntax_getArg(v_x_400_, v___x_415_);
lean_dec(v_x_400_);
v___x_417_ = l_Lean_Syntax_isNone(v___x_416_);
if (v___x_417_ == 0)
{
uint8_t v___x_418_; 
v___x_418_ = l_Lean_Syntax_matchesNull(v___x_416_, v___x_407_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_notStrictValueTk_414_);
lean_dec(v_id_408_);
v___x_419_ = l_Lean_Fmt_Error_partialFormatter;
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_a_402_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_notStrictValueTk_414_, v_id_408_, v_a_401_, v_a_402_);
return v___x_421_;
}
}
else
{
lean_object* v___x_422_; 
lean_dec(v___x_416_);
v___x_422_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_notStrictValueTk_414_, v_id_408_, v_a_401_, v_a_402_);
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotStrictValue___boxed(lean_object* v_x_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Fmt_fmtGrindNotStrictValue(v_x_423_, v_a_424_, v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1(){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_433_ = l_Lean_Fmt_fmtAttribute;
v___x_434_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNotStrictValue___closed__1));
v___x_435_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___closed__1));
v___x_436_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindNotStrictValue___boxed), 3, 0);
v___x_437_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_433_, v___x_434_, v___x_435_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1___boxed(lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1();
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsGround(lean_object* v_x_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsGround___closed__1));
lean_inc(v_x_447_);
v___x_451_ = l_Lean_Syntax_isOfKind(v_x_447_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v_x_447_);
v___x_452_ = l_Lean_Fmt_Error_partialFormatter;
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v_a_449_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v_id_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v_id_455_ = l_Lean_Syntax_getArg(v_x_447_, v___x_454_);
v___x_456_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_455_);
v___x_457_ = l_Lean_Syntax_isOfKind(v_id_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v_id_455_);
lean_dec(v_x_447_);
v___x_458_ = l_Lean_Fmt_Error_partialFormatter;
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_a_449_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v_isGroundTk_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v_isGroundTk_461_ = l_Lean_Syntax_getArg(v_x_447_, v___x_460_);
v___x_462_ = lean_unsigned_to_nat(2u);
v___x_463_ = l_Lean_Syntax_getArg(v_x_447_, v___x_462_);
lean_dec(v_x_447_);
v___x_464_ = l_Lean_Syntax_isNone(v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_Syntax_matchesNull(v___x_463_, v___x_454_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v_isGroundTk_461_);
lean_dec(v_id_455_);
v___x_466_ = l_Lean_Fmt_Error_partialFormatter;
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_a_449_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_isGroundTk_461_, v_id_455_, v_a_448_, v_a_449_);
return v___x_468_;
}
}
else
{
lean_object* v___x_469_; 
lean_dec(v___x_463_);
v___x_469_ = l_Lean_Fmt_fmtGrindIdentCnstr___redArg(v_isGroundTk_461_, v_id_455_, v_a_448_, v_a_449_);
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindIsGround___boxed(lean_object* v_x_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Fmt_fmtGrindIsGround(v_x_470_, v_a_471_, v_a_472_);
lean_dec_ref(v_a_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1(){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_480_ = l_Lean_Fmt_fmtAttribute;
v___x_481_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsGround___closed__1));
v___x_482_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___closed__1));
v___x_483_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindIsGround___boxed), 3, 0);
v___x_484_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_480_, v___x_481_, v___x_482_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1___boxed(lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1();
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSizeLt(lean_object* v_x_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSizeLt___closed__1));
lean_inc(v_x_497_);
v___x_501_ = l_Lean_Syntax_isOfKind(v_x_497_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_x_497_);
v___x_502_ = l_Lean_Fmt_Error_partialFormatter;
v___x_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_a_499_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v_id_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v_id_505_ = l_Lean_Syntax_getArg(v_x_497_, v___x_504_);
v___x_506_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_505_);
v___x_507_ = l_Lean_Syntax_isOfKind(v_id_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_id_505_);
lean_dec(v_x_497_);
v___x_508_ = l_Lean_Fmt_Error_partialFormatter;
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_a_499_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v_n_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_510_ = lean_unsigned_to_nat(3u);
v_n_511_ = l_Lean_Syntax_getArg(v_x_497_, v___x_510_);
v___x_512_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSizeLt___closed__3));
lean_inc(v_n_511_);
v___x_513_ = l_Lean_Syntax_isOfKind(v_n_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_n_511_);
lean_dec(v_id_505_);
lean_dec(v_x_497_);
v___x_514_ = l_Lean_Fmt_Error_partialFormatter;
v___x_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_a_499_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v_sizeTk_517_; lean_object* v___x_518_; lean_object* v_ltTk_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v_sizeTk_517_ = l_Lean_Syntax_getArg(v_x_497_, v___x_516_);
v___x_518_ = lean_unsigned_to_nat(2u);
v_ltTk_519_ = l_Lean_Syntax_getArg(v_x_497_, v___x_518_);
v___x_520_ = lean_unsigned_to_nat(4u);
v___x_521_ = l_Lean_Syntax_getArg(v_x_497_, v___x_520_);
lean_dec(v_x_497_);
v___x_522_ = l_Lean_Syntax_isNone(v___x_521_);
if (v___x_522_ == 0)
{
uint8_t v___x_523_; 
v___x_523_ = l_Lean_Syntax_matchesNull(v___x_521_, v___x_504_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_ltTk_519_);
lean_dec(v_sizeTk_517_);
lean_dec(v_n_511_);
lean_dec(v_id_505_);
v___x_524_ = l_Lean_Fmt_Error_partialFormatter;
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_a_499_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg(v_sizeTk_517_, v_id_505_, v_ltTk_519_, v_n_511_, v_a_498_, v_a_499_);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; 
lean_dec(v___x_521_);
v___x_527_ = l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg(v_sizeTk_517_, v_id_505_, v_ltTk_519_, v_n_511_, v_a_498_, v_a_499_);
return v___x_527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSizeLt___boxed(lean_object* v_x_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Fmt_fmtGrindSizeLt(v_x_528_, v_a_529_, v_a_530_);
lean_dec_ref(v_a_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1(){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_538_ = l_Lean_Fmt_fmtAttribute;
v___x_539_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSizeLt___closed__1));
v___x_540_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___closed__1));
v___x_541_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSizeLt___boxed), 3, 0);
v___x_542_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_538_, v___x_539_, v___x_540_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1___boxed(lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1();
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDepthLt(lean_object* v_x_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDepthLt___closed__1));
lean_inc(v_x_552_);
v___x_556_ = l_Lean_Syntax_isOfKind(v_x_552_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v_x_552_);
v___x_557_ = l_Lean_Fmt_Error_partialFormatter;
v___x_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_a_554_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v_id_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v_id_560_ = l_Lean_Syntax_getArg(v_x_552_, v___x_559_);
v___x_561_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_560_);
v___x_562_ = l_Lean_Syntax_isOfKind(v_id_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v_id_560_);
lean_dec(v_x_552_);
v___x_563_ = l_Lean_Fmt_Error_partialFormatter;
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_a_554_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; lean_object* v_n_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_565_ = lean_unsigned_to_nat(3u);
v_n_566_ = l_Lean_Syntax_getArg(v_x_552_, v___x_565_);
v___x_567_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSizeLt___closed__3));
lean_inc(v_n_566_);
v___x_568_ = l_Lean_Syntax_isOfKind(v_n_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_n_566_);
lean_dec(v_id_560_);
lean_dec(v_x_552_);
v___x_569_ = l_Lean_Fmt_Error_partialFormatter;
v___x_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v_a_554_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v_depthTk_572_; lean_object* v___x_573_; lean_object* v_ltTk_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v_depthTk_572_ = l_Lean_Syntax_getArg(v_x_552_, v___x_571_);
v___x_573_ = lean_unsigned_to_nat(2u);
v_ltTk_574_ = l_Lean_Syntax_getArg(v_x_552_, v___x_573_);
v___x_575_ = lean_unsigned_to_nat(4u);
v___x_576_ = l_Lean_Syntax_getArg(v_x_552_, v___x_575_);
lean_dec(v_x_552_);
v___x_577_ = l_Lean_Syntax_isNone(v___x_576_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; 
v___x_578_ = l_Lean_Syntax_matchesNull(v___x_576_, v___x_559_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_ltTk_574_);
lean_dec(v_depthTk_572_);
lean_dec(v_n_566_);
lean_dec(v_id_560_);
v___x_579_ = l_Lean_Fmt_Error_partialFormatter;
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_a_554_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg(v_depthTk_572_, v_id_560_, v_ltTk_574_, v_n_566_, v_a_553_, v_a_554_);
return v___x_581_;
}
}
else
{
lean_object* v___x_582_; 
lean_dec(v___x_576_);
v___x_582_ = l_Lean_Fmt_fmtGrindIdentLtCnstr___redArg(v_depthTk_572_, v_id_560_, v_ltTk_574_, v_n_566_, v_a_553_, v_a_554_);
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDepthLt___boxed(lean_object* v_x_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Fmt_fmtGrindDepthLt(v_x_583_, v_a_584_, v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1(){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_593_ = l_Lean_Fmt_fmtAttribute;
v___x_594_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDepthLt___closed__1));
v___x_595_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___closed__1));
v___x_596_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindDepthLt___boxed), 3, 0);
v___x_597_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_593_, v___x_594_, v___x_595_, v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1___boxed(lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1();
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindGenLt(lean_object* v_x_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Fmt_fmtGrindGenLt___closed__1));
lean_inc(v_x_607_);
v___x_611_ = l_Lean_Syntax_isOfKind(v_x_607_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_x_607_);
v___x_612_ = l_Lean_Fmt_Error_partialFormatter;
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v_a_609_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; lean_object* v_n_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_614_ = lean_unsigned_to_nat(2u);
v_n_615_ = l_Lean_Syntax_getArg(v_x_607_, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSizeLt___closed__3));
lean_inc(v_n_615_);
v___x_617_ = l_Lean_Syntax_isOfKind(v_n_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_n_615_);
lean_dec(v_x_607_);
v___x_618_ = l_Lean_Fmt_Error_partialFormatter;
v___x_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_a_609_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v_genTk_621_; lean_object* v___x_622_; lean_object* v_ltTk_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v_genTk_621_ = l_Lean_Syntax_getArg(v_x_607_, v___x_620_);
v___x_622_ = lean_unsigned_to_nat(1u);
v_ltTk_623_ = l_Lean_Syntax_getArg(v_x_607_, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(3u);
v___x_625_ = l_Lean_Syntax_getArg(v_x_607_, v___x_624_);
lean_dec(v_x_607_);
v___x_626_ = l_Lean_Syntax_isNone(v___x_625_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_Syntax_matchesNull(v___x_625_, v___x_622_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v_ltTk_623_);
lean_dec(v_genTk_621_);
lean_dec(v_n_615_);
v___x_628_ = l_Lean_Fmt_Error_partialFormatter;
v___x_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_a_609_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Fmt_fmtGrindLtCnstr___redArg(v_genTk_621_, v_ltTk_623_, v_n_615_, v_a_608_, v_a_609_);
return v___x_630_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v___x_625_);
v___x_631_ = l_Lean_Fmt_fmtGrindLtCnstr___redArg(v_genTk_621_, v_ltTk_623_, v_n_615_, v_a_608_, v_a_609_);
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindGenLt___boxed(lean_object* v_x_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Fmt_fmtGrindGenLt(v_x_632_, v_a_633_, v_a_634_);
lean_dec_ref(v_a_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1(){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_642_ = l_Lean_Fmt_fmtAttribute;
v___x_643_ = ((lean_object*)(l_Lean_Fmt_fmtGrindGenLt___closed__1));
v___x_644_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___closed__1));
v___x_645_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindGenLt___boxed), 3, 0);
v___x_646_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_642_, v___x_643_, v___x_644_, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1___boxed(lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1();
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindMaxInsts(lean_object* v_x_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMaxInsts___closed__1));
lean_inc(v_x_656_);
v___x_660_ = l_Lean_Syntax_isOfKind(v_x_656_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v_x_656_);
v___x_661_ = l_Lean_Fmt_Error_partialFormatter;
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v_a_658_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; lean_object* v_n_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_663_ = lean_unsigned_to_nat(2u);
v_n_664_ = l_Lean_Syntax_getArg(v_x_656_, v___x_663_);
v___x_665_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSizeLt___closed__3));
lean_inc(v_n_664_);
v___x_666_ = l_Lean_Syntax_isOfKind(v_n_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_n_664_);
lean_dec(v_x_656_);
v___x_667_ = l_Lean_Fmt_Error_partialFormatter;
v___x_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v_a_658_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v_maxInstsTk_670_; lean_object* v___x_671_; lean_object* v_ltTk_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v_maxInstsTk_670_ = l_Lean_Syntax_getArg(v_x_656_, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(1u);
v_ltTk_672_ = l_Lean_Syntax_getArg(v_x_656_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(3u);
v___x_674_ = l_Lean_Syntax_getArg(v_x_656_, v___x_673_);
lean_dec(v_x_656_);
v___x_675_ = l_Lean_Syntax_isNone(v___x_674_);
if (v___x_675_ == 0)
{
uint8_t v___x_676_; 
v___x_676_ = l_Lean_Syntax_matchesNull(v___x_674_, v___x_671_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v_ltTk_672_);
lean_dec(v_maxInstsTk_670_);
lean_dec(v_n_664_);
v___x_677_ = l_Lean_Fmt_Error_partialFormatter;
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v_a_658_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Fmt_fmtGrindLtCnstr___redArg(v_maxInstsTk_670_, v_ltTk_672_, v_n_664_, v_a_657_, v_a_658_);
return v___x_679_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v___x_674_);
v___x_680_ = l_Lean_Fmt_fmtGrindLtCnstr___redArg(v_maxInstsTk_670_, v_ltTk_672_, v_n_664_, v_a_657_, v_a_658_);
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindMaxInsts___boxed(lean_object* v_x_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Fmt_fmtGrindMaxInsts(v_x_681_, v_a_682_, v_a_683_);
lean_dec_ref(v_a_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1(){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_691_ = l_Lean_Fmt_fmtAttribute;
v___x_692_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMaxInsts___closed__1));
v___x_693_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___closed__1));
v___x_694_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindMaxInsts___boxed), 3, 0);
v___x_695_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_691_, v___x_692_, v___x_693_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1___boxed(lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1();
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindGuard(lean_object* v_x_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_Fmt_fmtGrindGuard___closed__1));
lean_inc(v_x_705_);
v___x_709_ = l_Lean_Syntax_isOfKind(v_x_705_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v_x_705_);
v___x_710_ = l_Lean_Fmt_Error_partialFormatter;
v___x_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_a_707_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; lean_object* v_guardTk_713_; lean_object* v___x_714_; lean_object* v_t_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v_guardTk_713_ = l_Lean_Syntax_getArg(v_x_705_, v___x_712_);
v___x_714_ = lean_unsigned_to_nat(1u);
v_t_715_ = l_Lean_Syntax_getArg(v_x_705_, v___x_714_);
v___x_716_ = lean_unsigned_to_nat(2u);
v___x_717_ = l_Lean_Syntax_getArg(v_x_705_, v___x_716_);
lean_dec(v_x_705_);
v___x_718_ = l_Lean_Syntax_isNone(v___x_717_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_Syntax_matchesNull(v___x_717_, v___x_714_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v_t_715_);
lean_dec(v_guardTk_713_);
v___x_720_ = l_Lean_Fmt_Error_partialFormatter;
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_a_707_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Fmt_fmtGrindTermCnstr___redArg(v_guardTk_713_, v_t_715_, v_a_706_, v_a_707_);
return v___x_722_;
}
}
else
{
lean_object* v___x_723_; 
lean_dec(v___x_717_);
v___x_723_ = l_Lean_Fmt_fmtGrindTermCnstr___redArg(v_guardTk_713_, v_t_715_, v_a_706_, v_a_707_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindGuard___boxed(lean_object* v_x_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Fmt_fmtGrindGuard(v_x_724_, v_a_725_, v_a_726_);
lean_dec_ref(v_a_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1(){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_734_ = l_Lean_Fmt_fmtAttribute;
v___x_735_ = ((lean_object*)(l_Lean_Fmt_fmtGrindGuard___closed__1));
v___x_736_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___closed__1));
v___x_737_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindGuard___boxed), 3, 0);
v___x_738_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_734_, v___x_735_, v___x_736_, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1___boxed(lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1();
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCheck(lean_object* v_x_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_Fmt_fmtGrindCheck___closed__1));
lean_inc(v_x_748_);
v___x_752_ = l_Lean_Syntax_isOfKind(v_x_748_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_x_748_);
v___x_753_ = l_Lean_Fmt_Error_partialFormatter;
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v_a_750_);
return v___x_754_;
}
else
{
lean_object* v___x_755_; lean_object* v_checkTk_756_; lean_object* v___x_757_; lean_object* v_t_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v_checkTk_756_ = l_Lean_Syntax_getArg(v_x_748_, v___x_755_);
v___x_757_ = lean_unsigned_to_nat(1u);
v_t_758_ = l_Lean_Syntax_getArg(v_x_748_, v___x_757_);
v___x_759_ = lean_unsigned_to_nat(2u);
v___x_760_ = l_Lean_Syntax_getArg(v_x_748_, v___x_759_);
lean_dec(v_x_748_);
v___x_761_ = l_Lean_Syntax_isNone(v___x_760_);
if (v___x_761_ == 0)
{
uint8_t v___x_762_; 
v___x_762_ = l_Lean_Syntax_matchesNull(v___x_760_, v___x_757_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec(v_t_758_);
lean_dec(v_checkTk_756_);
v___x_763_ = l_Lean_Fmt_Error_partialFormatter;
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v_a_750_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Fmt_fmtGrindTermCnstr___redArg(v_checkTk_756_, v_t_758_, v_a_749_, v_a_750_);
return v___x_765_;
}
}
else
{
lean_object* v___x_766_; 
lean_dec(v___x_760_);
v___x_766_ = l_Lean_Fmt_fmtGrindTermCnstr___redArg(v_checkTk_756_, v_t_758_, v_a_749_, v_a_750_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCheck___boxed(lean_object* v_x_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Fmt_fmtGrindCheck(v_x_767_, v_a_768_, v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1(){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_777_ = l_Lean_Fmt_fmtAttribute;
v___x_778_ = ((lean_object*)(l_Lean_Fmt_fmtGrindCheck___closed__1));
v___x_779_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___closed__1));
v___x_780_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindCheck___boxed), 3, 0);
v___x_781_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_777_, v___x_778_, v___x_779_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1___boxed(lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1();
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotDefEq(lean_object* v_x_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNotDefEq___closed__1));
lean_inc(v_x_791_);
v___x_795_ = l_Lean_Syntax_isOfKind(v_x_791_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_x_791_);
v___x_796_ = l_Lean_Fmt_Error_partialFormatter;
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v_a_793_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; lean_object* v_id_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v_id_799_ = l_Lean_Syntax_getArg(v_x_791_, v___x_798_);
v___x_800_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_799_);
v___x_801_ = l_Lean_Syntax_isOfKind(v_id_799_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v_id_799_);
lean_dec(v_x_791_);
v___x_802_ = l_Lean_Fmt_Error_partialFormatter;
v___x_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v_a_793_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; lean_object* v_eqTk_805_; lean_object* v___x_806_; lean_object* v_t_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_804_ = lean_unsigned_to_nat(1u);
v_eqTk_805_ = l_Lean_Syntax_getArg(v_x_791_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(2u);
v_t_807_ = l_Lean_Syntax_getArg(v_x_791_, v___x_806_);
v___x_808_ = lean_unsigned_to_nat(3u);
v___x_809_ = l_Lean_Syntax_getArg(v_x_791_, v___x_808_);
lean_dec(v_x_791_);
v___x_810_ = l_Lean_Syntax_isNone(v___x_809_);
if (v___x_810_ == 0)
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_Syntax_matchesNull(v___x_809_, v___x_804_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec(v_t_807_);
lean_dec(v_eqTk_805_);
lean_dec(v_id_799_);
v___x_812_ = l_Lean_Fmt_Error_partialFormatter;
v___x_813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v_a_793_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Fmt_fmtGrindEqCnstr___redArg(v_id_799_, v_eqTk_805_, v_t_807_, v_a_792_, v_a_793_);
return v___x_814_;
}
}
else
{
lean_object* v___x_815_; 
lean_dec(v___x_809_);
v___x_815_ = l_Lean_Fmt_fmtGrindEqCnstr___redArg(v_id_799_, v_eqTk_805_, v_t_807_, v_a_792_, v_a_793_);
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNotDefEq___boxed(lean_object* v_x_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Fmt_fmtGrindNotDefEq(v_x_816_, v_a_817_, v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1(){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_826_ = l_Lean_Fmt_fmtAttribute;
v___x_827_ = ((lean_object*)(l_Lean_Fmt_fmtGrindNotDefEq___closed__1));
v___x_828_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___closed__1));
v___x_829_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindNotDefEq___boxed), 3, 0);
v___x_830_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_826_, v___x_827_, v___x_828_, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1___boxed(lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1();
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDefEq(lean_object* v_x_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDefEq___closed__1));
lean_inc(v_x_840_);
v___x_844_ = l_Lean_Syntax_isOfKind(v_x_840_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_x_840_);
v___x_845_ = l_Lean_Fmt_Error_partialFormatter;
v___x_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v_a_842_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; lean_object* v_id_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_847_ = lean_unsigned_to_nat(0u);
v_id_848_ = l_Lean_Syntax_getArg(v_x_840_, v___x_847_);
v___x_849_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_id_848_);
v___x_850_ = l_Lean_Syntax_isOfKind(v_id_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_id_848_);
lean_dec(v_x_840_);
v___x_851_ = l_Lean_Fmt_Error_partialFormatter;
v___x_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v_a_842_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v_eqTk_854_; lean_object* v___x_855_; lean_object* v_t_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v_eqTk_854_ = l_Lean_Syntax_getArg(v_x_840_, v___x_853_);
v___x_855_ = lean_unsigned_to_nat(2u);
v_t_856_ = l_Lean_Syntax_getArg(v_x_840_, v___x_855_);
v___x_857_ = lean_unsigned_to_nat(3u);
v___x_858_ = l_Lean_Syntax_getArg(v_x_840_, v___x_857_);
lean_dec(v_x_840_);
v___x_859_ = l_Lean_Syntax_isNone(v___x_858_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; 
v___x_860_ = l_Lean_Syntax_matchesNull(v___x_858_, v___x_853_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec(v_t_856_);
lean_dec(v_eqTk_854_);
lean_dec(v_id_848_);
v___x_861_ = l_Lean_Fmt_Error_partialFormatter;
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_a_842_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Fmt_fmtGrindEqCnstr___redArg(v_id_848_, v_eqTk_854_, v_t_856_, v_a_841_, v_a_842_);
return v___x_863_;
}
}
else
{
lean_object* v___x_864_; 
lean_dec(v___x_858_);
v___x_864_ = l_Lean_Fmt_fmtGrindEqCnstr___redArg(v_id_848_, v_eqTk_854_, v_t_856_, v_a_841_, v_a_842_);
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDefEq___boxed(lean_object* v_x_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Fmt_fmtGrindDefEq(v_x_865_, v_a_866_, v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1(){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_875_ = l_Lean_Fmt_fmtAttribute;
v___x_876_ = ((lean_object*)(l_Lean_Fmt_fmtGrindDefEq___closed__1));
v___x_877_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___closed__1));
v___x_878_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindDefEq___boxed), 3, 0);
v___x_879_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_875_, v___x_876_, v___x_877_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1___boxed(lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1();
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPattern(lean_object* v_x_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPattern___closed__1));
lean_inc(v_x_904_);
v___x_908_ = l_Lean_Syntax_isOfKind(v_x_904_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_x_904_);
v___x_909_ = l_Lean_Fmt_Error_partialFormatter;
v___x_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v_a_906_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = l_Lean_Syntax_getArg(v_x_904_, v___x_911_);
v___x_913_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPattern___closed__4));
lean_inc(v___x_912_);
v___x_914_ = l_Lean_Syntax_isOfKind(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v___x_912_);
lean_dec(v_x_904_);
v___x_1015_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_a_906_);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; lean_object* v_grindPatternTk_1018_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v_whereTk_x3f_1027_; lean_object* v_cnstrs_x3f_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v_lbTk_x3f_1052_; lean_object* v_patName_x3f_1053_; lean_object* v_rbTk_x3f_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1017_ = lean_unsigned_to_nat(1u);
v_grindPatternTk_1018_ = l_Lean_Syntax_getArg(v_x_904_, v___x_1017_);
v___x_1084_ = lean_unsigned_to_nat(2u);
v___x_1085_ = l_Lean_Syntax_getArg(v_x_904_, v___x_1084_);
v___x_1086_ = l_Lean_Syntax_isNone(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1085_);
v___x_1088_ = l_Lean_Syntax_matchesNull(v___x_1085_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec(v___x_1085_);
lean_dec(v_grindPatternTk_1018_);
lean_dec(v___x_912_);
lean_dec(v_x_904_);
v___x_1089_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_a_906_);
return v___x_1090_;
}
else
{
lean_object* v_patName_x3f_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_patName_x3f_1091_ = l_Lean_Syntax_getArg(v___x_1085_, v___x_1017_);
v___x_1092_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v_patName_x3f_1091_);
v___x_1093_ = l_Lean_Syntax_isOfKind(v_patName_x3f_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec(v_patName_x3f_1091_);
lean_dec(v___x_1085_);
lean_dec(v_grindPatternTk_1018_);
lean_dec(v___x_912_);
lean_dec(v_x_904_);
v___x_1094_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_a_906_);
return v___x_1095_;
}
else
{
lean_object* v_lbTk_x3f_1096_; lean_object* v_rbTk_x3f_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_lbTk_x3f_1096_ = l_Lean_Syntax_getArg(v___x_1085_, v___x_911_);
v_rbTk_x3f_1097_ = l_Lean_Syntax_getArg(v___x_1085_, v___x_1084_);
lean_dec(v___x_1085_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_lbTk_x3f_1096_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_patName_x3f_1091_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_rbTk_x3f_1097_);
v_lbTk_x3f_1052_ = v___x_1098_;
v_patName_x3f_1053_ = v___x_1099_;
v_rbTk_x3f_1054_ = v___x_1100_;
v___y_1055_ = v_a_905_;
v___y_1056_ = v_a_906_;
goto v___jp_1051_;
}
}
}
else
{
lean_object* v___x_1101_; 
lean_dec(v___x_1085_);
v___x_1101_ = lean_box(0);
v_lbTk_x3f_1052_ = v___x_1101_;
v_patName_x3f_1053_ = v___x_1101_;
v_rbTk_x3f_1054_ = v___x_1101_;
v___y_1055_ = v_a_905_;
v___y_1056_ = v_a_906_;
goto v___jp_1051_;
}
v___jp_1019_:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Fmt_fmt(v___x_912_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
v_a_1033_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1031_, 2);
v___x_1034_ = l_Lean_Fmt_fmt(v_grindPatternTk_1018_, v___y_1029_, v_a_1033_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v_a_1036_; lean_object* v___x_1037_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
v_a_1036_ = lean_ctor_get(v___x_1034_, 1);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1034_, 2);
v___x_1037_ = l_Lean_Fmt_fmt_x3f(v___y_1025_, v___y_1029_, v_a_1036_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v_patterns_1041_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
v_a_1039_ = lean_ctor_get(v___x_1037_, 1);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1037_, 2);
v___x_1040_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPattern___closed__6));
v_patterns_1041_ = l_Lean_Syntax_getArgs(v___y_1023_);
lean_dec(v___y_1023_);
if (lean_obj_tag(v___y_1024_) == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_box(0);
v___y_973_ = v_patterns_1041_;
v___y_974_ = v___x_1040_;
v___y_975_ = v___y_1020_;
v___y_976_ = v_a_1035_;
v___y_977_ = v_whereTk_x3f_1027_;
v___y_978_ = v___y_1029_;
v___y_979_ = v_a_1039_;
v___y_980_ = v_a_1032_;
v___y_981_ = v___y_1021_;
v___y_982_ = v_a_1038_;
v___y_983_ = v_cnstrs_x3f_1028_;
v___y_984_ = v___y_1022_;
v___y_985_ = v___y_1026_;
v___y_986_ = v___x_1042_;
goto v___jp_972_;
}
else
{
lean_object* v_val_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_val_1043_ = lean_ctor_get(v___y_1024_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___y_1024_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___y_1024_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_val_1043_);
lean_dec(v___y_1024_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_val_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
v___y_973_ = v_patterns_1041_;
v___y_974_ = v___x_1040_;
v___y_975_ = v___y_1020_;
v___y_976_ = v_a_1035_;
v___y_977_ = v_whereTk_x3f_1027_;
v___y_978_ = v___y_1029_;
v___y_979_ = v_a_1039_;
v___y_980_ = v_a_1032_;
v___y_981_ = v___y_1021_;
v___y_982_ = v_a_1038_;
v___y_983_ = v_cnstrs_x3f_1028_;
v___y_984_ = v___y_1022_;
v___y_985_ = v___y_1026_;
v___y_986_ = v___x_1048_;
goto v___jp_972_;
}
}
}
}
else
{
lean_dec(v_a_1035_);
lean_dec(v_a_1032_);
lean_dec(v_cnstrs_x3f_1028_);
lean_dec(v_whereTk_x3f_1027_);
lean_dec(v___y_1026_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1021_);
lean_dec(v___y_1020_);
return v___x_1037_;
}
}
else
{
lean_dec(v_a_1032_);
lean_dec(v_cnstrs_x3f_1028_);
lean_dec(v_whereTk_x3f_1027_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1021_);
lean_dec(v___y_1020_);
return v___x_1034_;
}
}
else
{
lean_dec(v_cnstrs_x3f_1028_);
lean_dec(v_whereTk_x3f_1027_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec(v_grindPatternTk_1018_);
return v___x_1031_;
}
}
v___jp_1051_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1057_ = lean_unsigned_to_nat(3u);
v___x_1058_ = l_Lean_Syntax_getArg(v_x_904_, v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lean_Fmt_fmtGrindIsValue___closed__7));
lean_inc(v___x_1058_);
v___x_1060_ = l_Lean_Syntax_isOfKind(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec(v___x_1058_);
lean_dec(v_rbTk_x3f_1054_);
lean_dec(v_patName_x3f_1053_);
lean_dec(v_lbTk_x3f_1052_);
lean_dec(v_grindPatternTk_1018_);
lean_dec(v___x_912_);
lean_dec(v_x_904_);
v___x_1061_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___y_1056_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v_arrowTk_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1063_ = lean_unsigned_to_nat(4u);
v_arrowTk_1064_ = l_Lean_Syntax_getArg(v_x_904_, v___x_1063_);
v___x_1065_ = lean_unsigned_to_nat(5u);
v___x_1066_ = l_Lean_Syntax_getArg(v_x_904_, v___x_1065_);
v___x_1067_ = lean_unsigned_to_nat(6u);
v___x_1068_ = l_Lean_Syntax_getArg(v_x_904_, v___x_1067_);
lean_dec(v_x_904_);
v___x_1069_ = l_Lean_Syntax_isNone(v___x_1068_);
if (v___x_1069_ == 0)
{
uint8_t v___x_1070_; 
lean_inc(v___x_1068_);
v___x_1070_ = l_Lean_Syntax_matchesNull(v___x_1068_, v___x_1017_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v___x_1068_);
lean_dec(v___x_1066_);
lean_dec(v_arrowTk_1064_);
lean_dec(v___x_1058_);
lean_dec(v_rbTk_x3f_1054_);
lean_dec(v_patName_x3f_1053_);
lean_dec(v_lbTk_x3f_1052_);
lean_dec(v_grindPatternTk_1018_);
lean_dec(v___x_912_);
v___x_1071_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___y_1056_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1073_ = l_Lean_Syntax_getArg(v___x_1068_, v___x_911_);
lean_dec(v___x_1068_);
v___x_1074_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPattern___closed__8));
lean_inc(v___x_1073_);
v___x_1075_ = l_Lean_Syntax_isOfKind(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v___x_1073_);
lean_dec(v___x_1066_);
lean_dec(v_arrowTk_1064_);
lean_dec(v___x_1058_);
lean_dec(v_rbTk_x3f_1054_);
lean_dec(v_patName_x3f_1053_);
lean_dec(v_lbTk_x3f_1052_);
lean_dec(v_grindPatternTk_1018_);
lean_dec(v___x_912_);
v___x_1076_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___y_1056_);
return v___x_1077_;
}
else
{
lean_object* v_whereTk_x3f_1078_; lean_object* v___x_1079_; lean_object* v_cnstrs_x3f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_whereTk_x3f_1078_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_911_);
v___x_1079_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_1017_);
lean_dec(v___x_1073_);
v_cnstrs_x3f_1080_ = l_Lean_Syntax_getArgs(v___x_1079_);
lean_dec(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_whereTk_x3f_1078_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_cnstrs_x3f_1080_);
v___y_1020_ = v___x_1058_;
v___y_1021_ = v_rbTk_x3f_1054_;
v___y_1022_ = v___x_1057_;
v___y_1023_ = v___x_1066_;
v___y_1024_ = v_patName_x3f_1053_;
v___y_1025_ = v_lbTk_x3f_1052_;
v___y_1026_ = v_arrowTk_1064_;
v_whereTk_x3f_1027_ = v___x_1081_;
v_cnstrs_x3f_1028_ = v___x_1082_;
v___y_1029_ = v___y_1055_;
v___y_1030_ = v___y_1056_;
goto v___jp_1019_;
}
}
}
else
{
lean_object* v___x_1083_; 
lean_dec(v___x_1068_);
v___x_1083_ = lean_box(0);
v___y_1020_ = v___x_1058_;
v___y_1021_ = v_rbTk_x3f_1054_;
v___y_1022_ = v___x_1057_;
v___y_1023_ = v___x_1066_;
v___y_1024_ = v_patName_x3f_1053_;
v___y_1025_ = v_lbTk_x3f_1052_;
v___y_1026_ = v_arrowTk_1064_;
v_whereTk_x3f_1027_ = v___x_1083_;
v_cnstrs_x3f_1028_ = v___x_1083_;
v___y_1029_ = v___y_1055_;
v___y_1030_ = v___y_1056_;
goto v___jp_1019_;
}
}
}
}
v___jp_915_:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Fmt_fmtArray___redArg(v___y_929_, v___y_923_, v___y_922_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
v_a_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_930_, 2);
v___x_933_ = l_Lean_Fmt_fmt(v___y_917_, v___y_923_, v_a_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_962_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_a_935_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_962_ == 0)
{
v___x_937_ = v___x_933_;
v_isShared_938_ = v_isSharedCheck_962_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_962_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_939_ = lean_unsigned_to_nat(2u);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_941_ = lean_array_push(v___x_940_, v___y_924_);
v___x_942_ = lean_array_push(v___x_941_, v___y_919_);
v___x_943_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_942_);
lean_dec_ref(v___x_942_);
v___x_944_ = 0;
v___x_945_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_945_, 0, v___x_944_);
lean_ctor_set_uint8(v___x_945_, 1, v___x_914_);
v___x_946_ = l_Lean_Fmt_Layouts_bracketed(v___y_926_, v___y_921_, v___y_925_, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_947_, 0, v___x_943_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*1, v___x_914_);
v___x_948_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*1, v___x_914_);
v___x_949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_949_, 0, v_a_934_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_914_);
v___x_950_ = lean_mk_empty_array_with_capacity(v___y_927_);
v___x_951_ = lean_array_push(v___x_950_, v___x_947_);
v___x_952_ = lean_array_push(v___x_951_, v___x_948_);
v___x_953_ = lean_array_push(v___x_952_, v___x_949_);
v___x_954_ = l_Lean_Fmt_Layouts_blocks(v___x_953_, v___x_914_);
lean_dec_ref(v___x_953_);
lean_inc_ref(v___y_916_);
v___x_955_ = l_Lean_Fmt_Layouts_sepFill(v___y_916_, v___y_920_);
lean_dec_ref(v___y_920_);
v___x_956_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_954_, v___y_918_, v___x_955_, v___x_944_);
v___x_957_ = l_Lean_Fmt_Layouts_lines(v_a_931_);
lean_dec(v_a_931_);
v___x_958_ = l_Lean_Fmt_Layouts_whereDeclaration(v___x_956_, v___y_928_, v___x_957_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_958_);
v___x_960_ = v___x_937_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_a_935_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
lean_dec(v_a_931_);
lean_dec_ref(v___y_928_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v___y_918_);
return v___x_933_;
}
}
else
{
lean_object* v_a_963_; lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec_ref(v___y_928_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
v_a_963_ = lean_ctor_get(v___x_930_, 0);
v_a_964_ = lean_ctor_get(v___x_930_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_930_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_inc(v_a_963_);
lean_dec(v___x_930_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_963_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
v___jp_972_:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Fmt_fmt_x3f(v___y_986_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
v_a_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_987_, 2);
v___x_990_ = l_Lean_Fmt_fmt_x3f(v___y_981_, v___y_978_, v_a_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v_a_992_; lean_object* v___x_993_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
v_a_992_ = lean_ctor_get(v___x_990_, 1);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_990_, 2);
v___x_993_ = l_Lean_Fmt_fmt(v___y_985_, v___y_978_, v_a_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
v_a_995_ = lean_ctor_get(v___x_993_, 1);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_993_, 2);
v___x_996_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_973_, v___y_978_, v_a_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
v_a_998_ = lean_ctor_get(v___x_996_, 1);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_996_, 2);
v___x_999_ = l_Lean_Fmt_fmt_x3f(v___y_977_, v___y_978_, v_a_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
if (lean_obj_tag(v___y_983_) == 0)
{
lean_object* v_a_1000_; lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
v_a_1001_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_999_, 2);
v___x_1002_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPattern___closed__5));
v___y_916_ = v___y_974_;
v___y_917_ = v___y_975_;
v___y_918_ = v_a_994_;
v___y_919_ = v___y_976_;
v___y_920_ = v_a_997_;
v___y_921_ = v_a_988_;
v___y_922_ = v_a_1001_;
v___y_923_ = v___y_978_;
v___y_924_ = v___y_980_;
v___y_925_ = v_a_991_;
v___y_926_ = v___y_982_;
v___y_927_ = v___y_984_;
v___y_928_ = v_a_1000_;
v___y_929_ = v___x_1002_;
goto v___jp_915_;
}
else
{
lean_object* v_a_1003_; lean_object* v_a_1004_; lean_object* v_val_1005_; 
v_a_1003_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1003_);
v_a_1004_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_999_, 2);
v_val_1005_ = lean_ctor_get(v___y_983_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v___y_983_, 1);
v___y_916_ = v___y_974_;
v___y_917_ = v___y_975_;
v___y_918_ = v_a_994_;
v___y_919_ = v___y_976_;
v___y_920_ = v_a_997_;
v___y_921_ = v_a_988_;
v___y_922_ = v_a_1004_;
v___y_923_ = v___y_978_;
v___y_924_ = v___y_980_;
v___y_925_ = v_a_991_;
v___y_926_ = v___y_982_;
v___y_927_ = v___y_984_;
v___y_928_ = v_a_1003_;
v___y_929_ = v_val_1005_;
goto v___jp_915_;
}
}
else
{
lean_dec(v_a_997_);
lean_dec(v_a_994_);
lean_dec(v_a_991_);
lean_dec(v_a_988_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
return v___x_999_;
}
}
else
{
lean_object* v_a_1006_; lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_994_);
lean_dec(v_a_991_);
lean_dec(v_a_988_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
v_a_1006_ = lean_ctor_get(v___x_996_, 0);
v_a_1007_ = lean_ctor_get(v___x_996_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_996_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_inc(v_a_1006_);
lean_dec(v___x_996_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1006_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_dec(v_a_991_);
lean_dec(v_a_988_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_973_);
return v___x_993_;
}
}
else
{
lean_dec(v_a_988_);
lean_dec(v___y_985_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_973_);
return v___x_990_;
}
}
else
{
lean_dec(v___y_985_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_973_);
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPattern___boxed(lean_object* v_x_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Fmt_fmtGrindPattern(v_x_1102_, v_a_1103_, v_a_1104_);
lean_dec_ref(v_a_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1(){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1112_ = l_Lean_Fmt_fmtAttribute;
v___x_1113_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPattern___closed__1));
v___x_1114_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___closed__1));
v___x_1115_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindPattern___boxed), 3, 0);
v___x_1116_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1112_, v___x_1113_, v___x_1114_, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1___boxed(lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1();
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInitGrindNorm(lean_object* v_x_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_Lean_Fmt_fmtInitGrindNorm___closed__1));
lean_inc(v_x_1125_);
v___x_1129_ = l_Lean_Syntax_isOfKind(v_x_1125_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_x_1125_);
v___x_1130_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v_a_1127_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v_initGrindNormTk_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v_initGrindNormTk_1133_ = l_Lean_Syntax_getArg(v_x_1125_, v___x_1132_);
v___x_1134_ = l_Lean_Fmt_fmt(v_initGrindNormTk_1133_, v_a_1126_, v_a_1127_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_preTheorems_1139_; lean_object* v___x_1140_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
v_a_1136_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1134_, 2);
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = l_Lean_Syntax_getArg(v_x_1125_, v___x_1137_);
v_preTheorems_1139_ = l_Lean_Syntax_getArgs(v___x_1138_);
lean_dec(v___x_1138_);
v___x_1140_ = l_Lean_Fmt_fmtArray___redArg(v_preTheorems_1139_, v_a_1126_, v_a_1136_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v_pipeTk_1144_; lean_object* v___x_1145_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
v_a_1142_ = lean_ctor_get(v___x_1140_, 1);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1140_, 2);
v___x_1143_ = lean_unsigned_to_nat(2u);
v_pipeTk_1144_ = l_Lean_Syntax_getArg(v_x_1125_, v___x_1143_);
v___x_1145_ = l_Lean_Fmt_fmt(v_pipeTk_1144_, v_a_1126_, v_a_1142_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_postTheorems_1150_; lean_object* v___x_1151_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
v_a_1147_ = lean_ctor_get(v___x_1145_, 1);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1145_, 2);
v___x_1148_ = lean_unsigned_to_nat(3u);
v___x_1149_ = l_Lean_Syntax_getArg(v_x_1125_, v___x_1148_);
lean_dec(v_x_1125_);
v_postTheorems_1150_ = l_Lean_Syntax_getArgs(v___x_1149_);
lean_dec(v___x_1149_);
v___x_1151_ = l_Lean_Fmt_fmtArray___redArg(v_postTheorems_1150_, v_a_1126_, v_a_1147_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1168_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_a_1153_ = lean_ctor_get(v___x_1151_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1155_ = v___x_1151_;
v_isShared_1156_ = v_isSharedCheck_1168_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1168_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1137_);
lean_inc_ref(v___x_1157_);
v___x_1158_ = lean_array_push(v___x_1157_, v_a_1135_);
v___x_1159_ = l_Array_append___redArg(v___x_1158_, v_a_1141_);
lean_dec(v_a_1141_);
v___x_1160_ = lean_array_push(v___x_1157_, v_a_1146_);
v___x_1161_ = l_Array_append___redArg(v___x_1159_, v___x_1160_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = l_Array_append___redArg(v___x_1161_, v_a_1152_);
lean_dec(v_a_1152_);
v___x_1163_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_1162_, v___x_1129_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1163_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1164_);
v___x_1166_ = v___x_1155_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_a_1153_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_a_1146_);
lean_dec(v_a_1141_);
lean_dec(v_a_1135_);
v_a_1169_ = lean_ctor_get(v___x_1151_, 0);
v_a_1170_ = lean_ctor_get(v___x_1151_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1151_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_inc(v_a_1169_);
lean_dec(v___x_1151_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1169_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_dec(v_a_1141_);
lean_dec(v_a_1135_);
lean_dec(v_x_1125_);
return v___x_1145_;
}
}
else
{
lean_object* v_a_1178_; lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_a_1135_);
lean_dec(v_x_1125_);
v_a_1178_ = lean_ctor_get(v___x_1140_, 0);
v_a_1179_ = lean_ctor_get(v___x_1140_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1140_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_inc(v_a_1178_);
lean_dec(v___x_1140_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1178_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_dec(v_x_1125_);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInitGrindNorm___boxed(lean_object* v_x_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Fmt_fmtInitGrindNorm(v_x_1187_, v_a_1188_, v_a_1189_);
lean_dec_ref(v_a_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1197_ = l_Lean_Fmt_fmtAttribute;
v___x_1198_ = ((lean_object*)(l_Lean_Fmt_fmtInitGrindNorm___closed__1));
v___x_1199_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___closed__1));
v___x_1200_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInitGrindNorm___boxed), 3, 0);
v___x_1201_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1197_, v___x_1198_, v___x_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1___boxed(lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1();
return v_res_1203_;
}
}
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsValue___regBuiltin_Lean_Fmt_fmtGrindIsValue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsStrictValue___regBuiltin_Lean_Fmt_fmtGrindIsStrictValue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotValue___regBuiltin_Lean_Fmt_fmtGrindNotValue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotStrictValue___regBuiltin_Lean_Fmt_fmtGrindNotStrictValue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindIsGround___regBuiltin_Lean_Fmt_fmtGrindIsGround__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindSizeLt___regBuiltin_Lean_Fmt_fmtGrindSizeLt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDepthLt___regBuiltin_Lean_Fmt_fmtGrindDepthLt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGenLt___regBuiltin_Lean_Fmt_fmtGrindGenLt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindMaxInsts___regBuiltin_Lean_Fmt_fmtGrindMaxInsts__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindGuard___regBuiltin_Lean_Fmt_fmtGrindGuard__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindCheck___regBuiltin_Lean_Fmt_fmtGrindCheck__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindNotDefEq___regBuiltin_Lean_Fmt_fmtGrindNotDefEq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindDefEq___regBuiltin_Lean_Fmt_fmtGrindDefEq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtGrindPattern___regBuiltin_Lean_Fmt_fmtGrindPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser_0__Lean_Fmt_fmtInitGrindNorm___regBuiltin_Lean_Fmt_fmtInitGrindNorm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
