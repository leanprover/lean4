// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Tactic.Do.Syntax
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Tactic.Do.Syntax import Lean.Fmt.FmtM.CommonFormatters import Lean.Fmt.Formatters.Std.WP.Tactic import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtVCGenSimpArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtVCGenHead(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_tuple(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Fmt_joinAltPats___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_alt(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
static const lean_string_object l_Lean_Fmt_fmtMClear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtMClear___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtMClear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtMClear___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMClear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtMClear___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtMClear___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mclear"};
static const lean_object* l_Lean_Fmt_fmtMClear___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMClear___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtMClear___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMClear___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMClear___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMClear___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMClear___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMClear___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMClear___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__3_value),LEAN_SCALAR_PTR_LITERAL(107, 161, 32, 25, 224, 212, 229, 174)}};
static const lean_object* l_Lean_Fmt_fmtMClear___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtMClear___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtMClear___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtMClear___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtMClear___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtMClear___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtMClear___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtMClear___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMClear(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMClear___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtMClear"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 10, 31, 227, 151, 23, 205, 223)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMExact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mexact"};
static const lean_object* l_Lean_Fmt_fmtMExact___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMExact___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMExact___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMExact___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMExact___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMExact___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMExact___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMExact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMExact___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 177, 11, 252, 148, 218, 54, 90)}};
static const lean_object* l_Lean_Fmt_fmtMExact___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMExact___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMExact(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMExact___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtMExact"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 177, 229, 82, 113, 134, 50, 223)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mpure"};
static const lean_object* l_Lean_Fmt_fmtMPure___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMPure___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMPure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMPure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMPure___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMPure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMPure___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMPure___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 40, 78, 170, 57, 132, 109, 163)}};
static const lean_object* l_Lean_Fmt_fmtMPure___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMPure___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMPure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtMPure"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 135, 36, 29, 62, 66, 249, 80)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRenameI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mrenameI"};
static const lean_object* l_Lean_Fmt_fmtMRenameI___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRenameI___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRenameI___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRenameI___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRenameI___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRenameI___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRenameI___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRenameI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRenameI___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRenameI___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 187, 19, 96, 44, 239, 241, 167)}};
static const lean_object* l_Lean_Fmt_fmtMRenameI___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRenameI___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRenameI(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRenameI___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtMRenameI"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 97, 43, 77, 57, 111, 61, 8)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMSpecialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mspecialize"};
static const lean_object* l_Lean_Fmt_fmtMSpecialize___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMSpecialize___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMSpecialize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecialize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecialize___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecialize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecialize___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecialize___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 227, 189, 220, 199, 75, 123, 209)}};
static const lean_object* l_Lean_Fmt_fmtMSpecialize___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMSpecialize___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecialize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecialize___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtMSpecialize"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 41, 231, 146, 11, 211, 167, 239)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMSpecializePure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "mspecializePure"};
static const lean_object* l_Lean_Fmt_fmtMSpecializePure___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMSpecializePure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecializePure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecializePure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecializePure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 62, 145, 88, 202, 28, 127)}};
static const lean_object* l_Lean_Fmt_fmtMSpecializePure___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMSpecializePure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtMSpecializePure___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtMSpecializePure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Fmt_fmtMSpecializePure___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtMSpecializePure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecializePure___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecializePure___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecializePure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Fmt_fmtMSpecializePure___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtMSpecializePure___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecializePure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecializePure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtMSpecializePure"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 101, 23, 92, 62, 68, 84, 168)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mrefine"};
static const lean_object* l_Lean_Fmt_fmtMRefine___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefine___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefine___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefine___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefine___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefine___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefine___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefine___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 147, 116, 116, 185, 89, 229, 87)}};
static const lean_object* l_Lean_Fmt_fmtMRefine___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefine___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefine___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtMRefine"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 107, 123, 209, 200, 222, 159, 81)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mintro"};
static const lean_object* l_Lean_Fmt_fmtMIntro___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMIntro___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntro___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 222, 62, 246, 205, 225, 8, 203)}};
static const lean_object* l_Lean_Fmt_fmtMIntro___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMIntro___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtMIntro"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 199, 9, 221, 244, 19, 22, 198)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRevert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mrevert"};
static const lean_object* l_Lean_Fmt_fmtMRevert___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRevert___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRevert___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevert___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevert___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevert___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevert___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevert___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 105, 168, 208, 87, 76, 255, 172)}};
static const lean_object* l_Lean_Fmt_fmtMRevert___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRevert___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevert___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtMRevert"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 87, 11, 234, 203, 111, 16, 148)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMSpecNoBind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mspecNoBind"};
static const lean_object* l_Lean_Fmt_fmtMSpecNoBind___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMSpecNoBind___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMSpecNoBind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecNoBind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecNoBind___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecNoBind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecNoBind___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecNoBind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecNoBind___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMSpecNoBind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 86, 213, 46, 163, 23, 151, 189)}};
static const lean_object* l_Lean_Fmt_fmtMSpecNoBind___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMSpecNoBind___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecNoBind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecNoBind___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtMSpecNoBind"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 84, 109, 130, 69, 214, 180, 69)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMSpecNoSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mspecNoSimp"};
static const lean_object* l_Lean_Fmt_fmtMSpecNoSimp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMSpecNoSimp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMSpecNoSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecNoSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecNoSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecNoSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecNoSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpecNoSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpecNoSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMSpecNoSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 95, 246, 218, 2, 114, 192, 99)}};
static const lean_object* l_Lean_Fmt_fmtMSpecNoSimp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMSpecNoSimp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecNoSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecNoSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtMSpecNoSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 241, 55, 45, 64, 114, 161, 55)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mspec"};
static const lean_object* l_Lean_Fmt_fmtMSpec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMSpec___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpec___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpec___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpec___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMSpec___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 251, 147, 100, 37, 246, 67, 31)}};
static const lean_object* l_Lean_Fmt_fmtMSpec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMSpec___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtMSpec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 27, 250, 88, 248, 44, 114, 127)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mexists"};
static const lean_object* l_Lean_Fmt_fmtMExists___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMExists___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMExists___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMExists___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMExists___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMExists___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMExists___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMExists___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMExists___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 170, 199, 22, 25, 76, 35, 23)}};
static const lean_object* l_Lean_Fmt_fmtMExists___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMExists___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMExists___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtMExists___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMExists___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMExists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtMExists"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 56, 173, 146, 248, 115, 157, 171)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMDup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mdup"};
static const lean_object* l_Lean_Fmt_fmtMDup___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMDup___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMDup___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMDup___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMDup___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMDup___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMDup___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMDup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMDup___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMDup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 112, 88, 152, 42, 238, 157, 119)}};
static const lean_object* l_Lean_Fmt_fmtMDup___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMDup___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMDup(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMDup___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fmtMDup"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 140, 21, 183, 91, 31, 83, 237)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtMHaveLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtMHaveLike___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMHaveLike___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMHaveLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMHaveLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mhave"};
static const lean_object* l_Lean_Fmt_fmtMHave___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMHave___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 47, 33, 106, 233, 48, 163, 59)}};
static const lean_object* l_Lean_Fmt_fmtMHave___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMHave___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMHave(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMHave___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtMHave"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 72, 193, 158, 236, 253, 233, 75)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMReplace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mreplace"};
static const lean_object* l_Lean_Fmt_fmtMReplace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMReplace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMReplace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMReplace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMReplace___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMReplace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMReplace___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMReplace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMReplace___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMReplace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 100, 86, 218, 99, 164, 72, 83)}};
static const lean_object* l_Lean_Fmt_fmtMReplace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMReplace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMReplace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMReplace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtMReplace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 48, 120, 98, 240, 166, 168, 0)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCasesPatAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mcasesPatAlts"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatAlts___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatAlts___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatAlts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatAlts___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCasesPatAlts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 144, 167, 140, 164, 110, 77, 222)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatAlts___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatAlts___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatAlts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatAlts___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtMCasesPatAlts"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 44, 180, 252, 184, 119, 102, 12)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCasesPatOne___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mcasesPat_"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatOne___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatOne___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatOne___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatOne___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatOne___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 196, 52, 121, 17, 165, 127, 126)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatOne___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMCasesPatOne___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatOne___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatOne___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatOne___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatOne___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatOne___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatOne___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtMCasesPatOne"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 157, 62, 59, 25, 208, 39, 35)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatClear(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatClear___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtAtomic___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mcasesPat-"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(58, 11, 123, 49, 91, 91, 103, 235)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtMCasesPatClear"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 215, 178, 18, 28, 191, 93, 50)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCasesPatTuple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "mcasesPat⟨_⟩"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatTuple___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatTuple___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatTuple___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatTuple___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatTuple___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatTuple___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatTuple___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatTuple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatTuple___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCasesPatTuple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 121, 122, 163, 184, 200, 40, 28)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatTuple___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatTuple___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatTuple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatTuple___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtMCasesPatTuple"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 206, 189, 69, 59, 182, 28, 242)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCasesPatParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mcasesPat(_)"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatParen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatParen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatParen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCasesPatParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 228, 45, 90, 25, 77, 183, 251)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtMCasesPatParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 166, 164, 252, 141, 247, 221, 2)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCasesPatPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "mcasesPat⌜_⌝"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatPure___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatPure___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatPure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatPure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatPure___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatPure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatPure___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatPure___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCasesPatPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 36, 80, 160, 33, 204, 14, 109)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatPure___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatPure___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatPure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtMCasesPatPure"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 76, 109, 50, 227, 39, 202, 90)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCasesPatStateful___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "mcasesPat□_"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatStateful___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatStateful___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatStateful___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatStateful___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatStateful___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatStateful___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatStateful___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatStateful___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatStateful___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCasesPatStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 18, 113, 191, 78, 186, 91, 235)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatStateful___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatStateful___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatStateful(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatStateful___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtMCasesPatStateful"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 148, 213, 242, 176, 129, 208, 192)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mcasesPat%_"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 208, 54, 86, 176, 179, 232, 169)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatPureAbbrev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatPureAbbrev___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtMCasesPatPureAbbrev"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 38, 66, 7, 253, 200, 185, 248)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mcasesPat#_"};
static const lean_object* l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 139, 158, 197, 170, 161, 118, 161)}};
static const lean_object* l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatStatefulAbbrev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "fmtMCasesPatStatefulAbbrev"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 243, 112, 34, 189, 23, 227, 245)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mcases"};
static const lean_object* l_Lean_Fmt_fmtMCases___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMCases___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCases___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCases___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMCases___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 192, 12, 149, 146, 251, 197, 23)}};
static const lean_object* l_Lean_Fmt_fmtMCases___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMCases___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCases___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtMCases"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 195, 104, 156, 244, 7, 119, 19)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefinePatOne___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrefinePat_"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatOne___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatOne___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatOne___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatOne___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatOne___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatOne___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatOne___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatOne___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatOne___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 205, 252, 11, 203, 77, 12, 3)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatOne___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatOne___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatOne___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtMRefinePatOne"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 220, 125, 17, 105, 78, 92, 87)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefinePatTuple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "mrefinePat⟨_⟩"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatTuple___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatTuple___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatTuple___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatTuple___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatTuple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 252, 110, 106, 145, 210, 7, 196)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatTuple___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMRefinePatTuple___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrefinePats"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatTuple___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatTuple___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatTuple___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatTuple___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatTuple___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__2_value),LEAN_SCALAR_PTR_LITERAL(112, 173, 91, 190, 46, 156, 169, 121)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatTuple___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatTuple___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatTuple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatTuple___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtMRefinePatTuple"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 3, 55, 31, 124, 118, 10, 160)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefinePatParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mrefinePat(_)"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatParen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatParen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatParen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 235, 27, 55, 120, 135, 13, 209)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtMRefinePatParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 151, 159, 20, 41, 34, 102, 203)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefinePatPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "mrefinePat⌜_⌝"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatPure___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatPure___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatPure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatPure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatPure___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatPure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatPure___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatPure___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 247, 138, 95, 101, 152, 141, 145)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatPure___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatPure___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatPure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtMRefinePatPure"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 163, 15, 61, 186, 196, 253, 67)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefinePatStateful___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "mrefinePat□_"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatStateful___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatStateful___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatStateful___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatStateful___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatStateful___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatStateful___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatStateful___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatStateful___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatStateful___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatStateful___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 27, 205, 29, 81, 36, 207, 246)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatStateful___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatStateful___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatStateful(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatStateful___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtMRefinePatStateful"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 14, 240, 88, 97, 204, 243, 207)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefinePatHole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat\?_"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatHole___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatHole___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatHole___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatHole___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatHole___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatHole___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatHole___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatHole___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatHole___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 112, 196, 176, 199, 255, 59, 175)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatHole___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatHole___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatHole(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatHole___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtMRefinePatHole"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 141, 129, 101, 54, 22, 158, 146)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat%_"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 246, 182, 233, 244, 232, 234, 234)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatPureAbbrev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatPureAbbrev___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtMRefinePatPureAbbrev"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 146, 33, 22, 175, 82, 188, 130)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat#_"};
static const lean_object* l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 43, 185, 96, 20, 2, 38, 80)}};
static const lean_object* l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatStatefulAbbrev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "fmtMRefinePatStatefulAbbrev"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 244, 131, 126, 10, 79, 92, 44)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMIntroPatCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mintroPat_"};
static const lean_object* l_Lean_Fmt_fmtMIntroPatCases___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMIntroPatCases___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMIntroPatCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntroPatCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntroPatCases___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntroPatCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntroPatCases___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntroPatCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntroPatCases___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMIntroPatCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 197, 23, 48, 210, 183, 157, 165)}};
static const lean_object* l_Lean_Fmt_fmtMIntroPatCases___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMIntroPatCases___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntroPatCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntroPatCases___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtMIntroPatCases"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 34, 201, 255, 197, 144, 134, 66)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMIntroPatForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "mintroPat∀_"};
static const lean_object* l_Lean_Fmt_fmtMIntroPatForall___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMIntroPatForall___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMIntroPatForall___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntroPatForall___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntroPatForall___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntroPatForall___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntroPatForall___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMIntroPatForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMIntroPatForall___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMIntroPatForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 201, 27, 44, 199, 236, 234, 55)}};
static const lean_object* l_Lean_Fmt_fmtMIntroPatForall___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMIntroPatForall___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntroPatForall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntroPatForall___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtMIntroPatForall"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 252, 246, 31, 175, 18, 204, 9)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRevertPatOne___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrevertPat_"};
static const lean_object* l_Lean_Fmt_fmtMRevertPatOne___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRevertPatOne___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatOne___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatOne___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevertPatOne___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatOne___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevertPatOne___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatOne___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevertPatOne___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRevertPatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 56, 253, 143, 81, 27, 28, 109)}};
static const lean_object* l_Lean_Fmt_fmtMRevertPatOne___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRevertPatOne___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevertPatOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevertPatOne___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtMRevertPatOne"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 185, 184, 23, 123, 164, 137, 225)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMRevertPatForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "mrevertPat∀_"};
static const lean_object* l_Lean_Fmt_fmtMRevertPatForall___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatForall___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatForall___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatForall___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 101, 4, 189, 225, 175, 44, 14)}};
static const lean_object* l_Lean_Fmt_fmtMRevertPatForall___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMRevertPatForall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtMRevertPatForall___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtMRevertPatForall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtMRevertPatForall___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMRevertPatForall___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevertPatForall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevertPatForall___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtMRevertPatForall"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 228, 199, 241, 144, 110, 224, 218)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtVCAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcAlt"};
static const lean_object* l_Lean_Fmt_fmtVCAlt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtVCAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 45, 84, 214, 166, 18, 7, 59)}};
static const lean_object* l_Lean_Fmt_fmtVCAlt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtVCAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Fmt_fmtVCAlt___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtVCAlt___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlt___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlt___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Fmt_fmtVCAlt___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtVCAlt___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCAlt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtVCAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "vcAlts"};
static const lean_object* l_Lean_Fmt_fmtVCAlts___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtVCAlts___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtVCAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCAlts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCAlts___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtVCAlts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 11, 218, 136, 13, 239, 233, 239)}};
static const lean_object* l_Lean_Fmt_fmtVCAlts___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtVCAlts___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCAlts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCAlts___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtVCAlts"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 111, 109, 6, 245, 23, 215, 235)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMVCGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mvcgen"};
static const lean_object* l_Lean_Fmt_fmtMVCGen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 16, 249, 94, 239, 227, 109, 158)}};
static const lean_object* l_Lean_Fmt_fmtMVCGen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMVCGen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Fmt_fmtMVCGen___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Fmt_fmtMVCGen___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtMVCGen___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invariantAlts"};
static const lean_object* l_Lean_Fmt_fmtMVCGen___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGen___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 41, 254, 250, 50, 69, 99, 10)}};
static const lean_object* l_Lean_Fmt_fmtMVCGen___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtMVCGen___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMVCGen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMVCGen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtMVCGen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 161, 66, 14, 255, 165, 26, 249)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMVCGenHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mvcgenHint"};
static const lean_object* l_Lean_Fmt_fmtMVCGenHint___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMVCGenHint___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMVCGenHint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGenHint___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGenHint___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGenHint___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGenHint___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtMVCGenHint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMVCGenHint___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMVCGenHint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 105, 143, 226, 126, 5, 243, 226)}};
static const lean_object* l_Lean_Fmt_fmtMVCGenHint___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMVCGenHint___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMVCGenHint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMVCGenHint___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtMVCGenHint"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtMClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 17, 49, 82, 255, 193, 253, 140)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMClear(lean_object* v_x_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__4));
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
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
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
lean_object* v___x_26_; lean_object* v_mclearTk_27_; lean_object* v___x_28_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v_mclearTk_27_ = l_Lean_Syntax_getArg(v_x_13_, v___x_26_);
lean_dec(v_x_13_);
v___x_28_ = l_Lean_Fmt_fmt(v_mclearTk_27_, v_a_14_, v_a_15_);
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
lean_object* v_a_32_; lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_47_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_47_ == 0)
{
v___x_35_ = v___x_31_;
v_isShared_36_ = v_isSharedCheck_47_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_47_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_37_ = lean_unsigned_to_nat(2u);
v___x_38_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_39_ = lean_array_push(v___x_38_, v_a_29_);
v___x_40_ = lean_array_push(v___x_39_, v_a_32_);
v___x_41_ = 0;
v___x_42_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_42_, 0, v___x_23_);
lean_ctor_set_uint8(v___x_42_, 1, v___x_41_);
lean_ctor_set_uint8(v___x_42_, 2, v___x_41_);
lean_ctor_set_uint8(v___x_42_, 3, v___x_41_);
v___x_43_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_40_, v___x_42_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_43_);
v___x_45_ = v___x_35_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_a_33_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
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
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMClear___boxed(lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Fmt_fmtMClear(v_x_48_, v_a_49_, v_a_50_);
lean_dec_ref(v_a_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_59_ = l_Lean_Fmt_fmtAttribute;
v___x_60_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__4));
v___x_61_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___closed__2));
v___x_62_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMClear___boxed), 3, 0);
v___x_63_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_59_, v___x_60_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1___boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1();
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMExact(lean_object* v_x_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lean_Fmt_fmtMExact___closed__1));
lean_inc(v_x_72_);
v___x_76_ = l_Lean_Syntax_isOfKind(v_x_72_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_x_72_);
v___x_77_ = l_Lean_Fmt_Error_partialFormatter;
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v_a_74_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v_mexactTk_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v_mexactTk_80_ = l_Lean_Syntax_getArg(v_x_72_, v___x_79_);
v___x_81_ = l_Lean_Fmt_fmt(v_mexactTk_80_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v_a_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
v_a_83_ = lean_ctor_get(v___x_81_, 1);
lean_inc(v_a_83_);
lean_dec_ref_known(v___x_81_, 2);
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = l_Lean_Syntax_getArg(v_x_72_, v___x_84_);
lean_dec(v_x_72_);
v___x_86_ = l_Lean_Fmt_fmt(v___x_85_, v_a_73_, v_a_83_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_102_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_a_88_ = lean_ctor_get(v___x_86_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_102_ == 0)
{
v___x_90_ = v___x_86_;
v_isShared_91_ = v_isSharedCheck_102_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_102_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_92_ = lean_unsigned_to_nat(2u);
v___x_93_ = lean_mk_empty_array_with_capacity(v___x_92_);
v___x_94_ = lean_array_push(v___x_93_, v_a_82_);
v___x_95_ = lean_array_push(v___x_94_, v_a_87_);
v___x_96_ = 0;
v___x_97_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_97_, 0, v___x_76_);
lean_ctor_set_uint8(v___x_97_, 1, v___x_96_);
lean_ctor_set_uint8(v___x_97_, 2, v___x_96_);
lean_ctor_set_uint8(v___x_97_, 3, v___x_96_);
v___x_98_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_95_, v___x_97_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_98_);
v___x_100_ = v___x_90_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_a_88_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_dec(v_a_82_);
return v___x_86_;
}
}
else
{
lean_dec(v_x_72_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMExact___boxed(lean_object* v_x_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Fmt_fmtMExact(v_x_103_, v_a_104_, v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1(){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_113_ = l_Lean_Fmt_fmtAttribute;
v___x_114_ = ((lean_object*)(l_Lean_Fmt_fmtMExact___closed__1));
v___x_115_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___closed__1));
v___x_116_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMExact___boxed), 3, 0);
v___x_117_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_113_, v___x_114_, v___x_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1___boxed(lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1();
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMPure(lean_object* v_x_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lean_Fmt_fmtMPure___closed__1));
lean_inc(v_x_126_);
v___x_130_ = l_Lean_Syntax_isOfKind(v_x_126_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_x_126_);
v___x_131_ = l_Lean_Fmt_Error_partialFormatter;
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v_a_128_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = l_Lean_Syntax_getArg(v_x_126_, v___x_133_);
v___x_135_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
lean_inc(v___x_134_);
v___x_136_ = l_Lean_Syntax_isOfKind(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v___x_134_);
lean_dec(v_x_126_);
v___x_137_ = l_Lean_Fmt_Error_partialFormatter;
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_a_128_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v_mpureTk_140_; lean_object* v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(0u);
v_mpureTk_140_ = l_Lean_Syntax_getArg(v_x_126_, v___x_139_);
lean_dec(v_x_126_);
v___x_141_ = l_Lean_Fmt_fmt(v_mpureTk_140_, v_a_127_, v_a_128_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v_a_143_; lean_object* v___x_144_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
v_a_143_ = lean_ctor_get(v___x_141_, 1);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_141_, 2);
v___x_144_ = l_Lean_Fmt_fmt(v___x_134_, v_a_127_, v_a_143_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_160_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_a_146_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_160_ == 0)
{
v___x_148_ = v___x_144_;
v_isShared_149_ = v_isSharedCheck_160_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_160_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_150_ = lean_unsigned_to_nat(2u);
v___x_151_ = lean_mk_empty_array_with_capacity(v___x_150_);
v___x_152_ = lean_array_push(v___x_151_, v_a_142_);
v___x_153_ = lean_array_push(v___x_152_, v_a_145_);
v___x_154_ = 0;
v___x_155_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_155_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_155_, 1, v___x_154_);
lean_ctor_set_uint8(v___x_155_, 2, v___x_154_);
lean_ctor_set_uint8(v___x_155_, 3, v___x_154_);
v___x_156_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_153_, v___x_155_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_156_);
v___x_158_ = v___x_148_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_a_146_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_dec(v_a_142_);
return v___x_144_;
}
}
else
{
lean_dec(v___x_134_);
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMPure___boxed(lean_object* v_x_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Fmt_fmtMPure(v_x_161_, v_a_162_, v_a_163_);
lean_dec_ref(v_a_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1(){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = l_Lean_Fmt_fmtAttribute;
v___x_172_ = ((lean_object*)(l_Lean_Fmt_fmtMPure___closed__1));
v___x_173_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___closed__1));
v___x_174_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMPure___boxed), 3, 0);
v___x_175_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_171_, v___x_172_, v___x_173_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1___boxed(lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1();
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRenameI(lean_object* v_x_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Fmt_fmtMRenameI___closed__1));
lean_inc(v_x_184_);
v___x_188_ = l_Lean_Syntax_isOfKind(v_x_184_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_x_184_);
v___x_189_ = l_Lean_Fmt_Error_partialFormatter;
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_186_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v_mrenameITk_192_; lean_object* v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v_mrenameITk_192_ = l_Lean_Syntax_getArg(v_x_184_, v___x_191_);
v___x_193_ = l_Lean_Fmt_fmt(v_mrenameITk_192_, v_a_185_, v_a_186_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v_a_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_hs_198_; lean_object* v___x_199_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
v_a_195_ = lean_ctor_get(v___x_193_, 1);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_193_, 2);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = l_Lean_Syntax_getArg(v_x_184_, v___x_196_);
lean_dec(v_x_184_);
v_hs_198_ = l_Lean_Syntax_getArgs(v___x_197_);
lean_dec(v___x_197_);
v___x_199_ = l_Lean_Fmt_fmtArray___redArg(v_hs_198_, v_a_185_, v_a_195_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_214_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_a_201_ = lean_ctor_get(v___x_199_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_214_ == 0)
{
v___x_203_ = v___x_199_;
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_205_ = lean_mk_empty_array_with_capacity(v___x_196_);
v___x_206_ = lean_array_push(v___x_205_, v_a_194_);
v___x_207_ = l_Array_append___redArg(v___x_206_, v_a_200_);
lean_dec(v_a_200_);
v___x_208_ = 0;
v___x_209_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_209_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_209_, 1, v___x_208_);
lean_ctor_set_uint8(v___x_209_, 2, v___x_208_);
lean_ctor_set_uint8(v___x_209_, 3, v___x_208_);
v___x_210_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_207_, v___x_209_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_210_);
v___x_212_ = v___x_203_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_a_201_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_object* v_a_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec(v_a_194_);
v_a_215_ = lean_ctor_get(v___x_199_, 0);
v_a_216_ = lean_ctor_get(v___x_199_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_199_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_inc(v_a_215_);
lean_dec(v___x_199_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_215_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_dec(v_x_184_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRenameI___boxed(lean_object* v_x_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Fmt_fmtMRenameI(v_x_224_, v_a_225_, v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1(){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_234_ = l_Lean_Fmt_fmtAttribute;
v___x_235_ = ((lean_object*)(l_Lean_Fmt_fmtMRenameI___closed__1));
v___x_236_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___closed__1));
v___x_237_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRenameI___boxed), 3, 0);
v___x_238_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_234_, v___x_235_, v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1___boxed(lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1();
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecialize(lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecialize___closed__1));
lean_inc(v_x_247_);
v___x_251_ = l_Lean_Syntax_isOfKind(v_x_247_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v_x_247_);
v___x_252_ = l_Lean_Fmt_Error_partialFormatter;
v___x_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v_a_249_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = l_Lean_Syntax_getArg(v_x_247_, v___x_254_);
v___x_256_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
lean_inc(v___x_255_);
v___x_257_ = l_Lean_Syntax_isOfKind(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v___x_255_);
lean_dec(v_x_247_);
v___x_258_ = l_Lean_Fmt_Error_partialFormatter;
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_a_249_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; lean_object* v_mspecializeTk_261_; lean_object* v___x_262_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v_mspecializeTk_261_ = l_Lean_Syntax_getArg(v_x_247_, v___x_260_);
v___x_262_ = l_Lean_Fmt_fmt(v_mspecializeTk_261_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
v_a_264_ = lean_ctor_get(v___x_262_, 1);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_262_, 2);
v___x_265_ = l_Lean_Fmt_fmt(v___x_255_, v_a_248_, v_a_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_args_270_; lean_object* v___x_271_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
v_a_267_ = lean_ctor_get(v___x_265_, 1);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_265_, 2);
v___x_268_ = lean_unsigned_to_nat(2u);
v___x_269_ = l_Lean_Syntax_getArg(v_x_247_, v___x_268_);
lean_dec(v_x_247_);
v_args_270_ = l_Lean_Syntax_getArgs(v___x_269_);
lean_dec(v___x_269_);
v___x_271_ = l_Lean_Fmt_fmtArray___redArg(v_args_270_, v_a_248_, v_a_267_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_287_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_a_273_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_287_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_287_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_287_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_277_ = lean_mk_empty_array_with_capacity(v___x_268_);
v___x_278_ = lean_array_push(v___x_277_, v_a_263_);
v___x_279_ = lean_array_push(v___x_278_, v_a_266_);
v___x_280_ = l_Array_append___redArg(v___x_279_, v_a_272_);
lean_dec(v_a_272_);
v___x_281_ = 0;
v___x_282_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_282_, 0, v___x_257_);
lean_ctor_set_uint8(v___x_282_, 1, v___x_281_);
lean_ctor_set_uint8(v___x_282_, 2, v___x_281_);
lean_ctor_set_uint8(v___x_282_, 3, v___x_281_);
v___x_283_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_280_, v___x_282_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_283_);
v___x_285_ = v___x_275_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_a_273_);
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
lean_object* v_a_288_; lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_a_266_);
lean_dec(v_a_263_);
v_a_288_ = lean_ctor_get(v___x_271_, 0);
v_a_289_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_271_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_inc(v_a_288_);
lean_dec(v___x_271_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_288_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_dec(v_a_263_);
lean_dec(v_x_247_);
return v___x_265_;
}
}
else
{
lean_dec(v___x_255_);
lean_dec(v_x_247_);
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecialize___boxed(lean_object* v_x_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Fmt_fmtMSpecialize(v_x_297_, v_a_298_, v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1(){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_307_ = l_Lean_Fmt_fmtAttribute;
v___x_308_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecialize___closed__1));
v___x_309_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___closed__1));
v___x_310_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMSpecialize___boxed), 3, 0);
v___x_311_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_307_, v___x_308_, v___x_309_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1___boxed(lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1();
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecializePure(lean_object* v_x_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecializePure___closed__1));
lean_inc(v_x_327_);
v___x_331_ = l_Lean_Syntax_isOfKind(v_x_327_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_x_327_);
v___x_332_ = l_Lean_Fmt_Error_partialFormatter;
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_a_329_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = l_Lean_Syntax_getArg(v_x_327_, v___x_334_);
v___x_336_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecializePure___closed__4));
lean_inc(v___x_335_);
v___x_337_ = l_Lean_Syntax_isOfKind(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v___x_335_);
lean_dec(v_x_327_);
v___x_338_ = l_Lean_Fmt_Error_partialFormatter;
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_a_329_);
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_unsigned_to_nat(2u);
v___x_342_ = l_Lean_Syntax_getArg(v_x_327_, v___x_341_);
v___x_343_ = l_Lean_Syntax_matchesNull(v___x_342_, v___x_340_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v___x_335_);
lean_dec(v_x_327_);
v___x_344_ = l_Lean_Fmt_Error_partialFormatter;
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_a_329_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_346_ = lean_unsigned_to_nat(4u);
v___x_347_ = l_Lean_Syntax_getArg(v_x_327_, v___x_346_);
v___x_348_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
lean_inc(v___x_347_);
v___x_349_ = l_Lean_Syntax_isOfKind(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v___x_347_);
lean_dec(v___x_335_);
lean_dec(v_x_327_);
v___x_350_ = l_Lean_Fmt_Error_partialFormatter;
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_a_329_);
return v___x_351_;
}
else
{
lean_object* v_mspecializePureTk_352_; lean_object* v___x_353_; 
v_mspecializePureTk_352_ = l_Lean_Syntax_getArg(v_x_327_, v___x_340_);
v___x_353_ = l_Lean_Fmt_fmt(v_mspecializePureTk_352_, v_a_328_, v_a_329_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
v_a_355_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_353_, 2);
v___x_356_ = l_Lean_Syntax_getArg(v___x_335_, v___x_340_);
v___x_357_ = l_Lean_Fmt_fmt(v___x_356_, v_a_328_, v_a_355_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v_a_359_; lean_object* v___x_360_; lean_object* v_args_361_; lean_object* v___x_362_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
v_a_359_ = lean_ctor_get(v___x_357_, 1);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_357_, 2);
v___x_360_ = l_Lean_Syntax_getArg(v___x_335_, v___x_334_);
lean_dec(v___x_335_);
v_args_361_ = l_Lean_Syntax_getArgs(v___x_360_);
lean_dec(v___x_360_);
v___x_362_ = l_Lean_Fmt_fmtArray___redArg(v_args_361_, v_a_328_, v_a_359_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v_arrowTk_366_; lean_object* v___x_367_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
v_a_364_ = lean_ctor_get(v___x_362_, 1);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_362_, 2);
v___x_365_ = lean_unsigned_to_nat(3u);
v_arrowTk_366_ = l_Lean_Syntax_getArg(v_x_327_, v___x_365_);
lean_dec(v_x_327_);
v___x_367_ = l_Lean_Fmt_fmt(v_arrowTk_366_, v_a_328_, v_a_364_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v_a_369_; lean_object* v___x_370_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
v_a_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_367_, 2);
v___x_370_ = l_Lean_Fmt_fmt(v___x_347_, v_a_328_, v_a_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_390_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_a_372_ = lean_ctor_get(v___x_370_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_390_ == 0)
{
v___x_374_ = v___x_370_;
v_isShared_375_ = v_isSharedCheck_390_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_390_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_376_ = lean_mk_empty_array_with_capacity(v___x_334_);
v___x_377_ = lean_array_push(v___x_376_, v_a_358_);
v___x_378_ = l_Array_append___redArg(v___x_377_, v_a_363_);
lean_dec(v_a_363_);
v___x_379_ = 0;
v___x_380_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_380_, 0, v___x_349_);
lean_ctor_set_uint8(v___x_380_, 1, v___x_379_);
lean_ctor_set_uint8(v___x_380_, 2, v___x_379_);
lean_ctor_set_uint8(v___x_380_, 3, v___x_379_);
lean_inc_ref(v___x_380_);
v___x_381_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_378_, v___x_380_);
v___x_382_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_381_, v_a_368_, v_a_371_, v___x_379_);
v___x_383_ = lean_mk_empty_array_with_capacity(v___x_341_);
v___x_384_ = lean_array_push(v___x_383_, v_a_354_);
v___x_385_ = lean_array_push(v___x_384_, v___x_382_);
v___x_386_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_385_, v___x_380_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_386_);
v___x_388_ = v___x_374_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_a_372_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_dec(v_a_368_);
lean_dec(v_a_363_);
lean_dec(v_a_358_);
lean_dec(v_a_354_);
return v___x_370_;
}
}
else
{
lean_dec(v_a_363_);
lean_dec(v_a_358_);
lean_dec(v_a_354_);
lean_dec(v___x_347_);
return v___x_367_;
}
}
else
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v_a_358_);
lean_dec(v_a_354_);
lean_dec(v___x_347_);
lean_dec(v_x_327_);
v_a_391_ = lean_ctor_get(v___x_362_, 0);
v_a_392_ = lean_ctor_get(v___x_362_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_362_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_inc(v_a_391_);
lean_dec(v___x_362_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_391_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_dec(v_a_354_);
lean_dec(v___x_347_);
lean_dec(v___x_335_);
lean_dec(v_x_327_);
return v___x_357_;
}
}
else
{
lean_dec(v___x_347_);
lean_dec(v___x_335_);
lean_dec(v_x_327_);
return v___x_353_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecializePure___boxed(lean_object* v_x_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Fmt_fmtMSpecializePure(v_x_400_, v_a_401_, v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1(){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_410_ = l_Lean_Fmt_fmtAttribute;
v___x_411_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecializePure___closed__1));
v___x_412_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___closed__1));
v___x_413_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMSpecializePure___boxed), 3, 0);
v___x_414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_410_, v___x_411_, v___x_412_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1___boxed(lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1();
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefine(lean_object* v_x_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Fmt_fmtMRefine___closed__1));
lean_inc(v_x_423_);
v___x_427_ = l_Lean_Syntax_isOfKind(v_x_423_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v_x_423_);
v___x_428_ = l_Lean_Fmt_Error_partialFormatter;
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_a_425_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v_mrefineTk_431_; lean_object* v___x_432_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v_mrefineTk_431_ = l_Lean_Syntax_getArg(v_x_423_, v___x_430_);
v___x_432_ = l_Lean_Fmt_fmt(v_mrefineTk_431_, v_a_424_, v_a_425_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v_a_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
v_a_434_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_432_, 2);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = l_Lean_Syntax_getArg(v_x_423_, v___x_435_);
lean_dec(v_x_423_);
v___x_437_ = l_Lean_Fmt_fmt(v___x_436_, v_a_424_, v_a_434_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_453_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_a_439_ = lean_ctor_get(v___x_437_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_453_ == 0)
{
v___x_441_ = v___x_437_;
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_443_ = lean_unsigned_to_nat(2u);
v___x_444_ = lean_mk_empty_array_with_capacity(v___x_443_);
v___x_445_ = lean_array_push(v___x_444_, v_a_433_);
v___x_446_ = lean_array_push(v___x_445_, v_a_438_);
v___x_447_ = 0;
v___x_448_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_448_, 0, v___x_427_);
lean_ctor_set_uint8(v___x_448_, 1, v___x_447_);
lean_ctor_set_uint8(v___x_448_, 2, v___x_447_);
lean_ctor_set_uint8(v___x_448_, 3, v___x_447_);
v___x_449_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_446_, v___x_448_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_449_);
v___x_451_ = v___x_441_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_a_439_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_dec(v_a_433_);
return v___x_437_;
}
}
else
{
lean_dec(v_x_423_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefine___boxed(lean_object* v_x_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Fmt_fmtMRefine(v_x_454_, v_a_455_, v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1(){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_464_ = l_Lean_Fmt_fmtAttribute;
v___x_465_ = ((lean_object*)(l_Lean_Fmt_fmtMRefine___closed__1));
v___x_466_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___closed__1));
v___x_467_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefine___boxed), 3, 0);
v___x_468_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_464_, v___x_465_, v___x_466_, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1___boxed(lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1();
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntro(lean_object* v_x_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Fmt_fmtMIntro___closed__1));
lean_inc(v_x_477_);
v___x_481_ = l_Lean_Syntax_isOfKind(v_x_477_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_x_477_);
v___x_482_ = l_Lean_Fmt_Error_partialFormatter;
v___x_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_a_479_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; lean_object* v_mintroTk_485_; lean_object* v___x_486_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v_mintroTk_485_ = l_Lean_Syntax_getArg(v_x_477_, v___x_484_);
v___x_486_ = l_Lean_Fmt_fmt(v_mintroTk_485_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_pats_491_; lean_object* v___x_492_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
v_a_488_ = lean_ctor_get(v___x_486_, 1);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_486_, 2);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = l_Lean_Syntax_getArg(v_x_477_, v___x_489_);
lean_dec(v_x_477_);
v_pats_491_ = l_Lean_Syntax_getArgs(v___x_490_);
lean_dec(v___x_490_);
v___x_492_ = l_Lean_Fmt_fmtArray___redArg(v_pats_491_, v_a_478_, v_a_488_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_507_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_a_494_ = lean_ctor_get(v___x_492_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_507_ == 0)
{
v___x_496_ = v___x_492_;
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_498_ = lean_mk_empty_array_with_capacity(v___x_489_);
v___x_499_ = lean_array_push(v___x_498_, v_a_487_);
v___x_500_ = l_Array_append___redArg(v___x_499_, v_a_493_);
lean_dec(v_a_493_);
v___x_501_ = 0;
v___x_502_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_502_, 0, v___x_481_);
lean_ctor_set_uint8(v___x_502_, 1, v___x_501_);
lean_ctor_set_uint8(v___x_502_, 2, v___x_501_);
lean_ctor_set_uint8(v___x_502_, 3, v___x_501_);
v___x_503_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_500_, v___x_502_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_503_);
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_a_494_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_a_487_);
v_a_508_ = lean_ctor_get(v___x_492_, 0);
v_a_509_ = lean_ctor_get(v___x_492_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_492_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_inc(v_a_508_);
lean_dec(v___x_492_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_508_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_dec(v_x_477_);
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntro___boxed(lean_object* v_x_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Fmt_fmtMIntro(v_x_517_, v_a_518_, v_a_519_);
lean_dec_ref(v_a_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1(){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_527_ = l_Lean_Fmt_fmtAttribute;
v___x_528_ = ((lean_object*)(l_Lean_Fmt_fmtMIntro___closed__1));
v___x_529_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___closed__1));
v___x_530_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMIntro___boxed), 3, 0);
v___x_531_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_527_, v___x_528_, v___x_529_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1___boxed(lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1();
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevert(lean_object* v_x_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = ((lean_object*)(l_Lean_Fmt_fmtMRevert___closed__1));
lean_inc(v_x_540_);
v___x_544_ = l_Lean_Syntax_isOfKind(v_x_540_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_x_540_);
v___x_545_ = l_Lean_Fmt_Error_partialFormatter;
v___x_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v_a_542_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v_mrevertTk_548_; lean_object* v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v_mrevertTk_548_ = l_Lean_Syntax_getArg(v_x_540_, v___x_547_);
v___x_549_ = l_Lean_Fmt_fmt(v_mrevertTk_548_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_pats_554_; lean_object* v___x_555_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
v_a_551_ = lean_ctor_get(v___x_549_, 1);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_549_, 2);
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = l_Lean_Syntax_getArg(v_x_540_, v___x_552_);
lean_dec(v_x_540_);
v_pats_554_ = l_Lean_Syntax_getArgs(v___x_553_);
lean_dec(v___x_553_);
v___x_555_ = l_Lean_Fmt_fmtArray___redArg(v_pats_554_, v_a_541_, v_a_551_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_570_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_a_557_ = lean_ctor_get(v___x_555_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_570_ == 0)
{
v___x_559_ = v___x_555_;
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_561_ = lean_mk_empty_array_with_capacity(v___x_552_);
v___x_562_ = lean_array_push(v___x_561_, v_a_550_);
v___x_563_ = l_Array_append___redArg(v___x_562_, v_a_556_);
lean_dec(v_a_556_);
v___x_564_ = 0;
v___x_565_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_565_, 0, v___x_544_);
lean_ctor_set_uint8(v___x_565_, 1, v___x_564_);
lean_ctor_set_uint8(v___x_565_, 2, v___x_564_);
lean_ctor_set_uint8(v___x_565_, 3, v___x_564_);
v___x_566_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_563_, v___x_565_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_566_);
v___x_568_ = v___x_559_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_a_557_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_a_550_);
v_a_571_ = lean_ctor_get(v___x_555_, 0);
v_a_572_ = lean_ctor_get(v___x_555_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_555_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_inc(v_a_571_);
lean_dec(v___x_555_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_571_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_dec(v_x_540_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevert___boxed(lean_object* v_x_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Fmt_fmtMRevert(v_x_580_, v_a_581_, v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1(){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_590_ = l_Lean_Fmt_fmtAttribute;
v___x_591_ = ((lean_object*)(l_Lean_Fmt_fmtMRevert___closed__1));
v___x_592_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___closed__1));
v___x_593_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRevert___boxed), 3, 0);
v___x_594_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_590_, v___x_591_, v___x_592_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1___boxed(lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1();
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecNoBind(lean_object* v_x_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; 
v___x_606_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecNoBind___closed__1));
lean_inc(v_x_603_);
v___x_607_ = l_Lean_Syntax_isOfKind(v_x_603_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v_x_603_);
v___x_630_ = l_Lean_Fmt_Error_partialFormatter;
v___x_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v_a_605_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v_mspecNoBindTk_633_; lean_object* v_spec_x3f_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v_mspecNoBindTk_633_ = l_Lean_Syntax_getArg(v_x_603_, v___x_632_);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = l_Lean_Syntax_getArg(v_x_603_, v___x_652_);
lean_dec(v_x_603_);
v___x_654_ = l_Lean_Syntax_isNone(v___x_653_);
if (v___x_654_ == 0)
{
uint8_t v___x_655_; 
lean_inc(v___x_653_);
v___x_655_ = l_Lean_Syntax_matchesNull(v___x_653_, v___x_652_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v___x_653_);
lean_dec(v_mspecNoBindTk_633_);
v___x_656_ = l_Lean_Fmt_Error_partialFormatter;
v___x_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v_a_605_);
return v___x_657_;
}
else
{
lean_object* v_spec_x3f_658_; lean_object* v___x_659_; 
v_spec_x3f_658_ = l_Lean_Syntax_getArg(v___x_653_, v___x_632_);
lean_dec(v___x_653_);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v_spec_x3f_658_);
v_spec_x3f_635_ = v___x_659_;
v___y_636_ = v_a_604_;
v___y_637_ = v_a_605_;
goto v___jp_634_;
}
}
else
{
lean_object* v___x_660_; 
lean_dec(v___x_653_);
v___x_660_ = lean_box(0);
v_spec_x3f_635_ = v___x_660_;
v___y_636_ = v_a_604_;
v___y_637_ = v_a_605_;
goto v___jp_634_;
}
v___jp_634_:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Fmt_fmt(v_mspecNoBindTk_633_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_638_) == 0)
{
if (lean_obj_tag(v_spec_x3f_635_) == 0)
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
v_a_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_638_, 2);
v___x_641_ = lean_box(0);
v___y_609_ = v_a_640_;
v___y_610_ = v___y_636_;
v___y_611_ = v_a_639_;
v___y_612_ = v___x_641_;
goto v___jp_608_;
}
else
{
lean_object* v_a_642_; lean_object* v_a_643_; lean_object* v_val_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_a_642_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_642_);
v_a_643_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_638_, 2);
v_val_644_ = lean_ctor_get(v_spec_x3f_635_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_spec_x3f_635_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v_spec_x3f_635_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_val_644_);
lean_dec(v_spec_x3f_635_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_val_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
v___y_609_ = v_a_643_;
v___y_610_ = v___y_636_;
v___y_611_ = v_a_642_;
v___y_612_ = v___x_649_;
goto v___jp_608_;
}
}
}
}
else
{
lean_dec(v_spec_x3f_635_);
return v___x_638_;
}
}
}
v___jp_608_:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Fmt_fmt_x3f(v___y_612_, v___y_610_, v___y_609_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_629_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_a_615_ = lean_ctor_get(v___x_613_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_629_ == 0)
{
v___x_617_ = v___x_613_;
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_619_ = lean_unsigned_to_nat(2u);
v___x_620_ = lean_mk_empty_array_with_capacity(v___x_619_);
v___x_621_ = lean_array_push(v___x_620_, v___y_611_);
v___x_622_ = lean_array_push(v___x_621_, v_a_614_);
v___x_623_ = 0;
v___x_624_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_624_, 0, v___x_607_);
lean_ctor_set_uint8(v___x_624_, 1, v___x_623_);
lean_ctor_set_uint8(v___x_624_, 2, v___x_623_);
lean_ctor_set_uint8(v___x_624_, 3, v___x_623_);
v___x_625_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_622_, v___x_624_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_625_);
v___x_627_ = v___x_617_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_a_615_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
lean_dec_ref(v___y_611_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecNoBind___boxed(lean_object* v_x_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Fmt_fmtMSpecNoBind(v_x_661_, v_a_662_, v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1(){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_671_ = l_Lean_Fmt_fmtAttribute;
v___x_672_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecNoBind___closed__1));
v___x_673_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___closed__1));
v___x_674_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMSpecNoBind___boxed), 3, 0);
v___x_675_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_671_, v___x_672_, v___x_673_, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1___boxed(lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1();
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecNoSimp(lean_object* v_x_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_687_; uint8_t v___x_688_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; 
v___x_687_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecNoSimp___closed__1));
lean_inc(v_x_684_);
v___x_688_ = l_Lean_Syntax_isOfKind(v_x_684_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec(v_x_684_);
v___x_711_ = l_Lean_Fmt_Error_partialFormatter;
v___x_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v_a_686_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v_mspecNoSimpTk_714_; lean_object* v_spec_x3f_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_713_ = lean_unsigned_to_nat(0u);
v_mspecNoSimpTk_714_ = l_Lean_Syntax_getArg(v_x_684_, v___x_713_);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = l_Lean_Syntax_getArg(v_x_684_, v___x_733_);
lean_dec(v_x_684_);
v___x_735_ = l_Lean_Syntax_isNone(v___x_734_);
if (v___x_735_ == 0)
{
uint8_t v___x_736_; 
lean_inc(v___x_734_);
v___x_736_ = l_Lean_Syntax_matchesNull(v___x_734_, v___x_733_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec(v___x_734_);
lean_dec(v_mspecNoSimpTk_714_);
v___x_737_ = l_Lean_Fmt_Error_partialFormatter;
v___x_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v_a_686_);
return v___x_738_;
}
else
{
lean_object* v_spec_x3f_739_; lean_object* v___x_740_; 
v_spec_x3f_739_ = l_Lean_Syntax_getArg(v___x_734_, v___x_713_);
lean_dec(v___x_734_);
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v_spec_x3f_739_);
v_spec_x3f_716_ = v___x_740_;
v___y_717_ = v_a_685_;
v___y_718_ = v_a_686_;
goto v___jp_715_;
}
}
else
{
lean_object* v___x_741_; 
lean_dec(v___x_734_);
v___x_741_ = lean_box(0);
v_spec_x3f_716_ = v___x_741_;
v___y_717_ = v_a_685_;
v___y_718_ = v_a_686_;
goto v___jp_715_;
}
v___jp_715_:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Fmt_fmt(v_mspecNoSimpTk_714_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_719_) == 0)
{
if (lean_obj_tag(v_spec_x3f_716_) == 0)
{
lean_object* v_a_720_; lean_object* v_a_721_; lean_object* v___x_722_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
v_a_721_ = lean_ctor_get(v___x_719_, 1);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_719_, 2);
v___x_722_ = lean_box(0);
v___y_690_ = v_a_720_;
v___y_691_ = v_a_721_;
v___y_692_ = v___y_717_;
v___y_693_ = v___x_722_;
goto v___jp_689_;
}
else
{
lean_object* v_a_723_; lean_object* v_a_724_; lean_object* v_val_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_723_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_723_);
v_a_724_ = lean_ctor_get(v___x_719_, 1);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_719_, 2);
v_val_725_ = lean_ctor_get(v_spec_x3f_716_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_spec_x3f_716_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v_spec_x3f_716_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_val_725_);
lean_dec(v_spec_x3f_716_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_val_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v___y_690_ = v_a_723_;
v___y_691_ = v_a_724_;
v___y_692_ = v___y_717_;
v___y_693_ = v___x_730_;
goto v___jp_689_;
}
}
}
}
else
{
lean_dec(v_spec_x3f_716_);
return v___x_719_;
}
}
}
v___jp_689_:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Fmt_fmt_x3f(v___y_693_, v___y_692_, v___y_691_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_710_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_a_696_ = lean_ctor_get(v___x_694_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_710_ == 0)
{
v___x_698_ = v___x_694_;
v_isShared_699_ = v_isSharedCheck_710_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_710_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_700_ = lean_unsigned_to_nat(2u);
v___x_701_ = lean_mk_empty_array_with_capacity(v___x_700_);
v___x_702_ = lean_array_push(v___x_701_, v___y_690_);
v___x_703_ = lean_array_push(v___x_702_, v_a_695_);
v___x_704_ = 0;
v___x_705_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_705_, 0, v___x_688_);
lean_ctor_set_uint8(v___x_705_, 1, v___x_704_);
lean_ctor_set_uint8(v___x_705_, 2, v___x_704_);
lean_ctor_set_uint8(v___x_705_, 3, v___x_704_);
v___x_706_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_703_, v___x_705_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_706_);
v___x_708_ = v___x_698_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_a_696_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_dec_ref(v___y_690_);
return v___x_694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpecNoSimp___boxed(lean_object* v_x_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Fmt_fmtMSpecNoSimp(v_x_742_, v_a_743_, v_a_744_);
lean_dec_ref(v_a_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1(){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_752_ = l_Lean_Fmt_fmtAttribute;
v___x_753_ = ((lean_object*)(l_Lean_Fmt_fmtMSpecNoSimp___closed__1));
v___x_754_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___closed__1));
v___x_755_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMSpecNoSimp___boxed), 3, 0);
v___x_756_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_752_, v___x_753_, v___x_754_, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1___boxed(lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1();
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpec(lean_object* v_x_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; 
v___x_768_ = ((lean_object*)(l_Lean_Fmt_fmtMSpec___closed__1));
lean_inc(v_x_765_);
v___x_769_ = l_Lean_Syntax_isOfKind(v_x_765_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_x_765_);
v___x_792_ = l_Lean_Fmt_Error_partialFormatter;
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_a_767_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v_mspecTk_795_; lean_object* v_spec_x3f_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v_mspecTk_795_ = l_Lean_Syntax_getArg(v_x_765_, v___x_794_);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = l_Lean_Syntax_getArg(v_x_765_, v___x_814_);
lean_dec(v_x_765_);
v___x_816_ = l_Lean_Syntax_isNone(v___x_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; 
lean_inc(v___x_815_);
v___x_817_ = l_Lean_Syntax_matchesNull(v___x_815_, v___x_814_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec(v___x_815_);
lean_dec(v_mspecTk_795_);
v___x_818_ = l_Lean_Fmt_Error_partialFormatter;
v___x_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v_a_767_);
return v___x_819_;
}
else
{
lean_object* v_spec_x3f_820_; lean_object* v___x_821_; 
v_spec_x3f_820_ = l_Lean_Syntax_getArg(v___x_815_, v___x_794_);
lean_dec(v___x_815_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_spec_x3f_820_);
v_spec_x3f_797_ = v___x_821_;
v___y_798_ = v_a_766_;
v___y_799_ = v_a_767_;
goto v___jp_796_;
}
}
else
{
lean_object* v___x_822_; 
lean_dec(v___x_815_);
v___x_822_ = lean_box(0);
v_spec_x3f_797_ = v___x_822_;
v___y_798_ = v_a_766_;
v___y_799_ = v_a_767_;
goto v___jp_796_;
}
v___jp_796_:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Fmt_fmt(v_mspecTk_795_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
if (lean_obj_tag(v_spec_x3f_797_) == 0)
{
lean_object* v_a_801_; lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
v_a_802_ = lean_ctor_get(v___x_800_, 1);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_800_, 2);
v___x_803_ = lean_box(0);
v___y_771_ = v_a_802_;
v___y_772_ = v___y_798_;
v___y_773_ = v_a_801_;
v___y_774_ = v___x_803_;
goto v___jp_770_;
}
else
{
lean_object* v_a_804_; lean_object* v_a_805_; lean_object* v_val_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_a_804_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_804_);
v_a_805_ = lean_ctor_get(v___x_800_, 1);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_800_, 2);
v_val_806_ = lean_ctor_get(v_spec_x3f_797_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_spec_x3f_797_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v_spec_x3f_797_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_val_806_);
lean_dec(v_spec_x3f_797_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_val_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_771_ = v_a_805_;
v___y_772_ = v___y_798_;
v___y_773_ = v_a_804_;
v___y_774_ = v___x_811_;
goto v___jp_770_;
}
}
}
}
else
{
lean_dec(v_spec_x3f_797_);
return v___x_800_;
}
}
}
v___jp_770_:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Fmt_fmt_x3f(v___y_774_, v___y_772_, v___y_771_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_791_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_a_777_ = lean_ctor_get(v___x_775_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_791_ == 0)
{
v___x_779_ = v___x_775_;
v_isShared_780_ = v_isSharedCheck_791_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_791_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_781_ = lean_unsigned_to_nat(2u);
v___x_782_ = lean_mk_empty_array_with_capacity(v___x_781_);
v___x_783_ = lean_array_push(v___x_782_, v___y_773_);
v___x_784_ = lean_array_push(v___x_783_, v_a_776_);
v___x_785_ = 0;
v___x_786_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_786_, 0, v___x_769_);
lean_ctor_set_uint8(v___x_786_, 1, v___x_785_);
lean_ctor_set_uint8(v___x_786_, 2, v___x_785_);
lean_ctor_set_uint8(v___x_786_, 3, v___x_785_);
v___x_787_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_784_, v___x_786_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_787_);
v___x_789_ = v___x_779_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_a_777_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_dec_ref(v___y_773_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMSpec___boxed(lean_object* v_x_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Fmt_fmtMSpec(v_x_823_, v_a_824_, v_a_825_);
lean_dec_ref(v_a_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1(){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_833_ = l_Lean_Fmt_fmtAttribute;
v___x_834_ = ((lean_object*)(l_Lean_Fmt_fmtMSpec___closed__1));
v___x_835_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___closed__1));
v___x_836_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMSpec___boxed), 3, 0);
v___x_837_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_833_, v___x_834_, v___x_835_, v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1___boxed(lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1();
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMExists(lean_object* v_x_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = ((lean_object*)(l_Lean_Fmt_fmtMExists___closed__1));
lean_inc(v_x_847_);
v___x_851_ = l_Lean_Syntax_isOfKind(v_x_847_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_x_847_);
v___x_852_ = l_Lean_Fmt_Error_partialFormatter;
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_a_849_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v_mexistsTk_855_; lean_object* v___x_856_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v_mexistsTk_855_ = l_Lean_Syntax_getArg(v_x_847_, v___x_854_);
v___x_856_ = l_Lean_Fmt_fmt(v_mexistsTk_855_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_witnesses_861_; lean_object* v___x_862_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
v_a_858_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_856_, 2);
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = l_Lean_Syntax_getArg(v_x_847_, v___x_859_);
lean_dec(v_x_847_);
v_witnesses_861_ = l_Lean_Syntax_getArgs(v___x_860_);
lean_dec(v___x_860_);
v___x_862_ = l_Lean_Fmt_fmtTSepArray___redArg(v_witnesses_861_, v_a_848_, v_a_858_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_880_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_a_864_ = lean_ctor_get(v___x_862_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_880_ == 0)
{
v___x_866_ = v___x_862_;
v_isShared_867_ = v_isSharedCheck_880_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_880_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_868_ = ((lean_object*)(l_Lean_Fmt_fmtMExists___closed__2));
v___x_869_ = l_Lean_Fmt_Layouts_sepFill(v___x_868_, v_a_863_);
lean_dec(v_a_863_);
v___x_870_ = lean_unsigned_to_nat(2u);
v___x_871_ = lean_mk_empty_array_with_capacity(v___x_870_);
v___x_872_ = lean_array_push(v___x_871_, v_a_857_);
v___x_873_ = lean_array_push(v___x_872_, v___x_869_);
v___x_874_ = 0;
v___x_875_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_875_, 0, v___x_851_);
lean_ctor_set_uint8(v___x_875_, 1, v___x_874_);
lean_ctor_set_uint8(v___x_875_, 2, v___x_874_);
lean_ctor_set_uint8(v___x_875_, 3, v___x_874_);
v___x_876_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_873_, v___x_875_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_876_);
v___x_878_ = v___x_866_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_a_864_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec(v_a_857_);
v_a_881_ = lean_ctor_get(v___x_862_, 0);
v_a_882_ = lean_ctor_get(v___x_862_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_862_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_inc(v_a_881_);
lean_dec(v___x_862_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_dec(v_x_847_);
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMExists___boxed(lean_object* v_x_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Fmt_fmtMExists(v_x_890_, v_a_891_, v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1(){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_900_ = l_Lean_Fmt_fmtAttribute;
v___x_901_ = ((lean_object*)(l_Lean_Fmt_fmtMExists___closed__1));
v___x_902_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___closed__1));
v___x_903_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMExists___boxed), 3, 0);
v___x_904_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_900_, v___x_901_, v___x_902_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1___boxed(lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1();
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMDup(lean_object* v_x_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_Fmt_fmtMDup___closed__1));
lean_inc(v_x_913_);
v___x_917_ = l_Lean_Syntax_isOfKind(v_x_913_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_x_913_);
v___x_918_ = l_Lean_Fmt_Error_partialFormatter;
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v_a_915_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = l_Lean_Syntax_getArg(v_x_913_, v___x_920_);
v___x_922_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
lean_inc(v___x_921_);
v___x_923_ = l_Lean_Syntax_isOfKind(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v___x_921_);
lean_dec(v_x_913_);
v___x_924_ = l_Lean_Fmt_Error_partialFormatter;
v___x_925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v_a_915_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_unsigned_to_nat(3u);
v___x_927_ = l_Lean_Syntax_getArg(v_x_913_, v___x_926_);
lean_inc(v___x_927_);
v___x_928_ = l_Lean_Syntax_isOfKind(v___x_927_, v___x_922_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v___x_927_);
lean_dec(v___x_921_);
lean_dec(v_x_913_);
v___x_929_ = l_Lean_Fmt_Error_partialFormatter;
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v_a_915_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v_mdupTk_932_; lean_object* v___x_933_; 
v___x_931_ = lean_unsigned_to_nat(0u);
v_mdupTk_932_ = l_Lean_Syntax_getArg(v_x_913_, v___x_931_);
v___x_933_ = l_Lean_Fmt_fmt(v_mdupTk_932_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_936_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
v_a_935_ = lean_ctor_get(v___x_933_, 1);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_933_, 2);
v___x_936_ = l_Lean_Fmt_fmt(v___x_921_, v_a_914_, v_a_935_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v_arrowTk_940_; lean_object* v___x_941_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
v_a_938_ = lean_ctor_get(v___x_936_, 1);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_936_, 2);
v___x_939_ = lean_unsigned_to_nat(2u);
v_arrowTk_940_ = l_Lean_Syntax_getArg(v_x_913_, v___x_939_);
lean_dec(v_x_913_);
v___x_941_ = l_Lean_Fmt_fmt(v_arrowTk_940_, v_a_914_, v_a_938_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v_a_943_; lean_object* v___x_944_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
v_a_943_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_941_, 2);
v___x_944_ = l_Lean_Fmt_fmt(v___x_927_, v_a_914_, v_a_943_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_960_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_a_946_ = lean_ctor_get(v___x_944_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_960_ == 0)
{
v___x_948_ = v___x_944_;
v_isShared_949_ = v_isSharedCheck_960_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_960_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_950_ = 0;
v___x_951_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_937_, v_a_942_, v_a_945_, v___x_950_);
v___x_952_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_953_ = lean_array_push(v___x_952_, v_a_934_);
v___x_954_ = lean_array_push(v___x_953_, v___x_951_);
v___x_955_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_955_, 0, v___x_928_);
lean_ctor_set_uint8(v___x_955_, 1, v___x_950_);
lean_ctor_set_uint8(v___x_955_, 2, v___x_950_);
lean_ctor_set_uint8(v___x_955_, 3, v___x_950_);
v___x_956_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_954_, v___x_955_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_956_);
v___x_958_ = v___x_948_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_a_946_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
else
{
lean_dec(v_a_942_);
lean_dec(v_a_937_);
lean_dec(v_a_934_);
return v___x_944_;
}
}
else
{
lean_dec(v_a_937_);
lean_dec(v_a_934_);
lean_dec(v___x_927_);
return v___x_941_;
}
}
else
{
lean_dec(v_a_934_);
lean_dec(v___x_927_);
lean_dec(v_x_913_);
return v___x_936_;
}
}
else
{
lean_dec(v___x_927_);
lean_dec(v___x_921_);
lean_dec(v_x_913_);
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMDup___boxed(lean_object* v_x_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Fmt_fmtMDup(v_x_961_, v_a_962_, v_a_963_);
lean_dec_ref(v_a_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1(){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_971_ = l_Lean_Fmt_fmtAttribute;
v___x_972_ = ((lean_object*)(l_Lean_Fmt_fmtMDup___closed__1));
v___x_973_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___closed__1));
v___x_974_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMDup___boxed), 3, 0);
v___x_975_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_971_, v___x_972_, v___x_973_, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1___boxed(lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1();
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMHaveLike(lean_object* v_keywordTk_981_, lean_object* v_h_982_, lean_object* v_typeAscriptionTk_x3f_983_, lean_object* v_type_x3f_984_, lean_object* v_colonEqTk_985_, lean_object* v_body_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Fmt_fmt(v_keywordTk_981_, v_a_987_, v_a_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v___x_992_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
v_a_991_ = lean_ctor_get(v___x_989_, 1);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_989_, 2);
v___x_992_ = l_Lean_Fmt_fmt(v_h_982_, v_a_987_, v_a_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v_a_994_; lean_object* v___x_995_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
v_a_994_ = lean_ctor_get(v___x_992_, 1);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_992_, 2);
v___x_995_ = l_Lean_Fmt_fmt_x3f(v_typeAscriptionTk_x3f_983_, v_a_987_, v_a_994_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
v_a_997_ = lean_ctor_get(v___x_995_, 1);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_995_, 2);
v___x_998_ = l_Lean_Fmt_fmt_x3f(v_type_x3f_984_, v_a_987_, v_a_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
v_a_1000_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_998_, 2);
v___x_1001_ = l_Lean_Fmt_fmt(v_colonEqTk_985_, v_a_987_, v_a_1000_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
v_a_1003_ = lean_ctor_get(v___x_1001_, 1);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1001_, 2);
v___x_1004_ = l_Lean_Fmt_fmt(v_body_986_, v_a_987_, v_a_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1019_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_a_1006_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1008_ = v___x_1004_;
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1010_ = 0;
v___x_1011_ = ((lean_object*)(l_Lean_Fmt_fmtMHaveLike___closed__0));
v___x_1012_ = l_Lean_Fmt_Layouts_typeAscription(v_a_993_, v_a_996_, v_a_999_, v___x_1011_);
v___x_1013_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1014_ = l_Lean_Fmt_Layouts_letDecl(v_a_990_, v___x_1013_, v___x_1012_, v___x_1010_);
v___x_1015_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_1014_, v_a_1002_, v_a_1005_, v___x_1010_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1015_);
v___x_1017_ = v___x_1008_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_a_1006_);
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
lean_dec(v_a_1002_);
lean_dec(v_a_999_);
lean_dec(v_a_996_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
return v___x_1004_;
}
}
else
{
lean_dec(v_a_999_);
lean_dec(v_a_996_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec(v_body_986_);
return v___x_1001_;
}
}
else
{
lean_dec(v_a_996_);
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec(v_body_986_);
lean_dec(v_colonEqTk_985_);
return v___x_998_;
}
}
else
{
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec(v_body_986_);
lean_dec(v_colonEqTk_985_);
lean_dec(v_type_x3f_984_);
return v___x_995_;
}
}
else
{
lean_dec(v_a_990_);
lean_dec(v_body_986_);
lean_dec(v_colonEqTk_985_);
lean_dec(v_type_x3f_984_);
lean_dec(v_typeAscriptionTk_x3f_983_);
return v___x_992_;
}
}
else
{
lean_dec(v_body_986_);
lean_dec(v_colonEqTk_985_);
lean_dec(v_type_x3f_984_);
lean_dec(v_typeAscriptionTk_x3f_983_);
lean_dec(v_h_982_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMHaveLike___boxed(lean_object* v_keywordTk_1020_, lean_object* v_h_1021_, lean_object* v_typeAscriptionTk_x3f_1022_, lean_object* v_type_x3f_1023_, lean_object* v_colonEqTk_1024_, lean_object* v_body_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Fmt_fmtMHaveLike(v_keywordTk_1020_, v_h_1021_, v_typeAscriptionTk_x3f_1022_, v_type_x3f_1023_, v_colonEqTk_1024_, v_body_1025_, v_a_1026_, v_a_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMHave(lean_object* v_x_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Fmt_fmtMHave___closed__1));
lean_inc(v_x_1035_);
v___x_1039_ = l_Lean_Syntax_isOfKind(v_x_1035_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec(v_x_1035_);
v___x_1040_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_a_1037_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = l_Lean_Syntax_getArg(v_x_1035_, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
lean_inc(v___x_1043_);
v___x_1045_ = l_Lean_Syntax_isOfKind(v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v___x_1043_);
lean_dec(v_x_1035_);
v___x_1046_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_a_1037_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; lean_object* v_mhaveTk_1049_; lean_object* v_typeAscriptionTk_x3f_1051_; lean_object* v_type_x3f_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1048_ = lean_unsigned_to_nat(0u);
v_mhaveTk_1049_ = l_Lean_Syntax_getArg(v_x_1035_, v___x_1048_);
v___x_1070_ = lean_unsigned_to_nat(2u);
v___x_1071_ = l_Lean_Syntax_getArg(v_x_1035_, v___x_1070_);
v___x_1072_ = l_Lean_Syntax_isNone(v___x_1071_);
if (v___x_1072_ == 0)
{
uint8_t v___x_1073_; 
lean_inc(v___x_1071_);
v___x_1073_ = l_Lean_Syntax_matchesNull(v___x_1071_, v___x_1070_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v___x_1071_);
lean_dec(v_mhaveTk_1049_);
lean_dec(v___x_1043_);
lean_dec(v_x_1035_);
v___x_1074_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_a_1037_);
return v___x_1075_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_1076_; lean_object* v_type_x3f_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_typeAscriptionTk_x3f_1076_ = l_Lean_Syntax_getArg(v___x_1071_, v___x_1048_);
v_type_x3f_1077_ = l_Lean_Syntax_getArg(v___x_1071_, v___x_1042_);
lean_dec(v___x_1071_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_typeAscriptionTk_x3f_1076_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_type_x3f_1077_);
v_typeAscriptionTk_x3f_1051_ = v___x_1078_;
v_type_x3f_1052_ = v___x_1079_;
v___y_1053_ = v_a_1036_;
v___y_1054_ = v_a_1037_;
goto v___jp_1050_;
}
}
else
{
lean_object* v___x_1080_; 
lean_dec(v___x_1071_);
v___x_1080_ = lean_box(0);
v_typeAscriptionTk_x3f_1051_ = v___x_1080_;
v_type_x3f_1052_ = v___x_1080_;
v___y_1053_ = v_a_1036_;
v___y_1054_ = v_a_1037_;
goto v___jp_1050_;
}
v___jp_1050_:
{
lean_object* v___x_1055_; lean_object* v_colonEqTk_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_unsigned_to_nat(3u);
v_colonEqTk_1056_ = l_Lean_Syntax_getArg(v_x_1035_, v___x_1055_);
v___x_1057_ = lean_unsigned_to_nat(4u);
v___x_1058_ = l_Lean_Syntax_getArg(v_x_1035_, v___x_1057_);
lean_dec(v_x_1035_);
if (lean_obj_tag(v_type_x3f_1052_) == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = l_Lean_Fmt_fmtMHaveLike(v_mhaveTk_1049_, v___x_1043_, v_typeAscriptionTk_x3f_1051_, v___x_1059_, v_colonEqTk_1056_, v___x_1058_, v___y_1053_, v___y_1054_);
return v___x_1060_;
}
else
{
lean_object* v_val_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_val_1061_ = lean_ctor_get(v_type_x3f_1052_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_type_x3f_1052_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_type_x3f_1052_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_val_1061_);
lean_dec(v_type_x3f_1052_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_val_1061_);
v___x_1066_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Fmt_fmtMHaveLike(v_mhaveTk_1049_, v___x_1043_, v_typeAscriptionTk_x3f_1051_, v___x_1066_, v_colonEqTk_1056_, v___x_1058_, v___y_1053_, v___y_1054_);
return v___x_1067_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMHave___boxed(lean_object* v_x_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Fmt_fmtMHave(v_x_1081_, v_a_1082_, v_a_1083_);
lean_dec_ref(v_a_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1(){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1091_ = l_Lean_Fmt_fmtAttribute;
v___x_1092_ = ((lean_object*)(l_Lean_Fmt_fmtMHave___closed__1));
v___x_1093_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___closed__1));
v___x_1094_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMHave___boxed), 3, 0);
v___x_1095_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1091_, v___x_1092_, v___x_1093_, v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1___boxed(lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1();
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMReplace(lean_object* v_x_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_Fmt_fmtMReplace___closed__1));
lean_inc(v_x_1104_);
v___x_1108_ = l_Lean_Syntax_isOfKind(v_x_1104_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec(v_x_1104_);
v___x_1109_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_a_1106_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = l_Lean_Syntax_getArg(v_x_1104_, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
lean_inc(v___x_1112_);
v___x_1114_ = l_Lean_Syntax_isOfKind(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v___x_1112_);
lean_dec(v_x_1104_);
v___x_1115_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_a_1106_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; lean_object* v_mreplaceTk_1118_; lean_object* v_typeAscriptionTk_x3f_1120_; lean_object* v_type_x3f_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1117_ = lean_unsigned_to_nat(0u);
v_mreplaceTk_1118_ = l_Lean_Syntax_getArg(v_x_1104_, v___x_1117_);
v___x_1139_ = lean_unsigned_to_nat(2u);
v___x_1140_ = l_Lean_Syntax_getArg(v_x_1104_, v___x_1139_);
v___x_1141_ = l_Lean_Syntax_isNone(v___x_1140_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; 
lean_inc(v___x_1140_);
v___x_1142_ = l_Lean_Syntax_matchesNull(v___x_1140_, v___x_1139_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v___x_1140_);
lean_dec(v_mreplaceTk_1118_);
lean_dec(v___x_1112_);
lean_dec(v_x_1104_);
v___x_1143_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v_a_1106_);
return v___x_1144_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_1145_; lean_object* v_type_x3f_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_typeAscriptionTk_x3f_1145_ = l_Lean_Syntax_getArg(v___x_1140_, v___x_1117_);
v_type_x3f_1146_ = l_Lean_Syntax_getArg(v___x_1140_, v___x_1111_);
lean_dec(v___x_1140_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_typeAscriptionTk_x3f_1145_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_type_x3f_1146_);
v_typeAscriptionTk_x3f_1120_ = v___x_1147_;
v_type_x3f_1121_ = v___x_1148_;
v___y_1122_ = v_a_1105_;
v___y_1123_ = v_a_1106_;
goto v___jp_1119_;
}
}
else
{
lean_object* v___x_1149_; 
lean_dec(v___x_1140_);
v___x_1149_ = lean_box(0);
v_typeAscriptionTk_x3f_1120_ = v___x_1149_;
v_type_x3f_1121_ = v___x_1149_;
v___y_1122_ = v_a_1105_;
v___y_1123_ = v_a_1106_;
goto v___jp_1119_;
}
v___jp_1119_:
{
lean_object* v___x_1124_; lean_object* v_colonEqTk_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1124_ = lean_unsigned_to_nat(3u);
v_colonEqTk_1125_ = l_Lean_Syntax_getArg(v_x_1104_, v___x_1124_);
v___x_1126_ = lean_unsigned_to_nat(4u);
v___x_1127_ = l_Lean_Syntax_getArg(v_x_1104_, v___x_1126_);
lean_dec(v_x_1104_);
if (lean_obj_tag(v_type_x3f_1121_) == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = l_Lean_Fmt_fmtMHaveLike(v_mreplaceTk_1118_, v___x_1112_, v_typeAscriptionTk_x3f_1120_, v___x_1128_, v_colonEqTk_1125_, v___x_1127_, v___y_1122_, v___y_1123_);
return v___x_1129_;
}
else
{
lean_object* v_val_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v_val_1130_ = lean_ctor_get(v_type_x3f_1121_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_type_x3f_1121_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v_type_x3f_1121_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_val_1130_);
lean_dec(v_type_x3f_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_val_1130_);
v___x_1135_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Fmt_fmtMHaveLike(v_mreplaceTk_1118_, v___x_1112_, v_typeAscriptionTk_x3f_1120_, v___x_1135_, v_colonEqTk_1125_, v___x_1127_, v___y_1122_, v___y_1123_);
return v___x_1136_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMReplace___boxed(lean_object* v_x_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Fmt_fmtMReplace(v_x_1150_, v_a_1151_, v_a_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1(){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1160_ = l_Lean_Fmt_fmtAttribute;
v___x_1161_ = ((lean_object*)(l_Lean_Fmt_fmtMReplace___closed__1));
v___x_1162_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___closed__1));
v___x_1163_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMReplace___boxed), 3, 0);
v___x_1164_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1160_, v___x_1161_, v___x_1162_, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1___boxed(lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1();
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatAlts(lean_object* v_x_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatAlts___closed__1));
lean_inc(v_x_1173_);
v___x_1177_ = l_Lean_Syntax_isOfKind(v_x_1173_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v_x_1173_);
v___x_1178_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v_a_1175_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_pats_1182_; lean_object* v___x_1183_; 
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = l_Lean_Syntax_getArg(v_x_1173_, v___x_1180_);
lean_dec(v_x_1173_);
v_pats_1182_ = l_Lean_Syntax_getArgs(v___x_1181_);
lean_dec(v___x_1181_);
v___x_1183_ = l_Lean_Fmt_fmtTSepArray___redArg(v_pats_1182_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1196_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_a_1185_ = lean_ctor_get(v___x_1183_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1187_ = v___x_1183_;
v_isShared_1188_ = v_isSharedCheck_1196_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1196_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1189_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1190_ = l_Lean_Fmt_joinAltPats___redArg(v___x_1189_, v_a_1184_);
lean_dec(v_a_1184_);
v___x_1191_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_1190_, v___x_1177_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1191_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1192_);
v___x_1194_ = v___x_1187_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_a_1185_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1197_ = lean_ctor_get(v___x_1183_, 0);
v_a_1198_ = lean_ctor_get(v___x_1183_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1183_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_inc(v_a_1197_);
lean_dec(v___x_1183_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1197_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatAlts___boxed(lean_object* v_x_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Fmt_fmtMCasesPatAlts(v_x_1206_, v_a_1207_, v_a_1208_);
lean_dec_ref(v_a_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1(){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1216_ = l_Lean_Fmt_fmtAttribute;
v___x_1217_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatAlts___closed__1));
v___x_1218_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___closed__1));
v___x_1219_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCasesPatAlts___boxed), 3, 0);
v___x_1220_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1216_, v___x_1217_, v___x_1218_, v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1___boxed(lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1();
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatOne(lean_object* v_x_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__1));
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
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = l_Lean_Syntax_getArg(v_x_1233_, v___x_1240_);
lean_dec(v_x_1233_);
v___x_1242_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_1241_);
v___x_1243_ = l_Lean_Syntax_isOfKind(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec(v___x_1241_);
v___x_1244_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v_a_1235_);
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Fmt_fmt(v___x_1241_, v_a_1234_, v_a_1235_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatOne___boxed(lean_object* v_x_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Fmt_fmtMCasesPatOne(v_x_1247_, v_a_1248_, v_a_1249_);
lean_dec_ref(v_a_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1(){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1257_ = l_Lean_Fmt_fmtAttribute;
v___x_1258_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__1));
v___x_1259_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___closed__1));
v___x_1260_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCasesPatOne___boxed), 3, 0);
v___x_1261_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1257_, v___x_1258_, v___x_1259_, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1___boxed(lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1();
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatClear(lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_Fmt_fmtAtomic(v_a_1264_, v_a_1265_, v_a_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatClear___boxed(lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Fmt_fmtMCasesPatClear(v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec_ref(v_a_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1(){
_start:
{
lean_object* v___f_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___f_1285_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__0));
v___x_1286_ = l_Lean_Fmt_fmtAttribute;
v___x_1287_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__2));
v___x_1288_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___closed__4));
v___x_1289_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1286_, v___x_1287_, v___x_1288_, v___f_1285_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1___boxed(lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1();
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatTuple(lean_object* v_x_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatTuple___closed__1));
lean_inc(v_x_1298_);
v___x_1302_ = l_Lean_Syntax_isOfKind(v_x_1298_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_x_1298_);
v___x_1303_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_a_1300_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; lean_object* v_lbTk_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v_lbTk_1306_ = l_Lean_Syntax_getArg(v_x_1298_, v___x_1305_);
v___x_1307_ = l_Lean_Fmt_fmt(v_lbTk_1306_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_pats_1312_; lean_object* v___x_1313_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
v_a_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1307_, 2);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = l_Lean_Syntax_getArg(v_x_1298_, v___x_1310_);
v_pats_1312_ = l_Lean_Syntax_getArgs(v___x_1311_);
lean_dec(v___x_1311_);
v___x_1313_ = l_Lean_Fmt_fmtTSepArray___redArg(v_pats_1312_, v_a_1299_, v_a_1309_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v_rbTk_1317_; lean_object* v___x_1318_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
v_a_1315_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1313_, 2);
v___x_1316_ = lean_unsigned_to_nat(2u);
v_rbTk_1317_ = l_Lean_Syntax_getArg(v_x_1298_, v___x_1316_);
lean_dec(v_x_1298_);
v___x_1318_ = l_Lean_Fmt_fmt(v_rbTk_1317_, v_a_1299_, v_a_1315_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1329_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_a_1320_ = lean_ctor_get(v___x_1318_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1322_ = v___x_1318_;
v_isShared_1323_ = v_isSharedCheck_1329_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1329_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1324_ = ((lean_object*)(l_Lean_Fmt_fmtMExists___closed__2));
v___x_1325_ = l_Lean_Fmt_Layouts_tuple(v___x_1324_, v_a_1308_, v_a_1314_, v_a_1319_);
lean_dec(v_a_1314_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1325_);
v___x_1327_ = v___x_1322_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_a_1320_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_dec(v_a_1314_);
lean_dec(v_a_1308_);
return v___x_1318_;
}
}
else
{
lean_object* v_a_1330_; lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_a_1308_);
lean_dec(v_x_1298_);
v_a_1330_ = lean_ctor_get(v___x_1313_, 0);
v_a_1331_ = lean_ctor_get(v___x_1313_, 1);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1313_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_inc(v_a_1330_);
lean_dec(v___x_1313_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1330_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_dec(v_x_1298_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatTuple___boxed(lean_object* v_x_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Fmt_fmtMCasesPatTuple(v_x_1339_, v_a_1340_, v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1(){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1349_ = l_Lean_Fmt_fmtAttribute;
v___x_1350_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatTuple___closed__1));
v___x_1351_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___closed__1));
v___x_1352_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCasesPatTuple___boxed), 3, 0);
v___x_1353_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1349_, v___x_1350_, v___x_1351_, v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1___boxed(lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1();
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatParen(lean_object* v_x_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatParen___closed__1));
lean_inc(v_x_1362_);
v___x_1366_ = l_Lean_Syntax_isOfKind(v_x_1362_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec(v_x_1362_);
v___x_1367_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v_a_1364_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = l_Lean_Syntax_getArg(v_x_1362_, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatAlts___closed__1));
lean_inc(v___x_1370_);
v___x_1372_ = l_Lean_Syntax_isOfKind(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec(v___x_1370_);
lean_dec(v_x_1362_);
v___x_1373_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set(v___x_1374_, 1, v_a_1364_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v_lbTk_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(0u);
v_lbTk_1376_ = l_Lean_Syntax_getArg(v_x_1362_, v___x_1375_);
v___x_1377_ = l_Lean_Fmt_fmt(v_lbTk_1376_, v_a_1363_, v_a_1364_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v_a_1379_; lean_object* v___x_1380_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
v_a_1379_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1377_, 2);
v___x_1380_ = l_Lean_Fmt_fmt(v___x_1370_, v_a_1363_, v_a_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v_rbTk_1384_; lean_object* v___x_1385_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
v_a_1382_ = lean_ctor_get(v___x_1380_, 1);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1380_, 2);
v___x_1383_ = lean_unsigned_to_nat(2u);
v_rbTk_1384_ = l_Lean_Syntax_getArg(v_x_1362_, v___x_1383_);
lean_dec(v_x_1362_);
v___x_1385_ = l_Lean_Fmt_fmt(v_rbTk_1384_, v_a_1363_, v_a_1382_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_a_1387_ = lean_ctor_get(v___x_1385_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1389_ = v___x_1385_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = l_Lean_Fmt_Layouts_parens(v_a_1378_, v_a_1381_, v_a_1386_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_a_1387_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
lean_dec(v_a_1381_);
lean_dec(v_a_1378_);
return v___x_1385_;
}
}
else
{
lean_dec(v_a_1378_);
lean_dec(v_x_1362_);
return v___x_1380_;
}
}
else
{
lean_dec(v___x_1370_);
lean_dec(v_x_1362_);
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatParen___boxed(lean_object* v_x_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Fmt_fmtMCasesPatParen(v_x_1396_, v_a_1397_, v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1(){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1406_ = l_Lean_Fmt_fmtAttribute;
v___x_1407_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatParen___closed__1));
v___x_1408_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___closed__1));
v___x_1409_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCasesPatParen___boxed), 3, 0);
v___x_1410_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1406_, v___x_1407_, v___x_1408_, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1___boxed(lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1();
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatPure(lean_object* v_x_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatPure___closed__1));
lean_inc(v_x_1419_);
v___x_1423_ = l_Lean_Syntax_isOfKind(v_x_1419_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_x_1419_);
v___x_1424_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v_a_1421_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1426_ = lean_unsigned_to_nat(1u);
v___x_1427_ = l_Lean_Syntax_getArg(v_x_1419_, v___x_1426_);
v___x_1428_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_1427_);
v___x_1429_ = l_Lean_Syntax_isOfKind(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v___x_1427_);
lean_dec(v_x_1419_);
v___x_1430_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v_a_1421_);
return v___x_1431_;
}
else
{
lean_object* v___x_1432_; lean_object* v_lbTk_1433_; lean_object* v___x_1434_; 
v___x_1432_ = lean_unsigned_to_nat(0u);
v_lbTk_1433_ = l_Lean_Syntax_getArg(v_x_1419_, v___x_1432_);
v___x_1434_ = l_Lean_Fmt_fmt(v_lbTk_1433_, v_a_1420_, v_a_1421_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
v_a_1436_ = lean_ctor_get(v___x_1434_, 1);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1434_, 2);
v___x_1437_ = l_Lean_Fmt_fmt(v___x_1427_, v_a_1420_, v_a_1436_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v_a_1439_; lean_object* v___x_1440_; lean_object* v_rbTk_1441_; lean_object* v___x_1442_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
v_a_1439_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1437_, 2);
v___x_1440_ = lean_unsigned_to_nat(2u);
v_rbTk_1441_ = l_Lean_Syntax_getArg(v_x_1419_, v___x_1440_);
lean_dec(v_x_1419_);
v___x_1442_ = l_Lean_Fmt_fmt(v_rbTk_1441_, v_a_1420_, v_a_1439_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_a_1444_ = lean_ctor_get(v___x_1442_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v___x_1442_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = l_Lean_Fmt_Layouts_parens(v_a_1435_, v_a_1438_, v_a_1443_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_a_1444_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_dec(v_a_1438_);
lean_dec(v_a_1435_);
return v___x_1442_;
}
}
else
{
lean_dec(v_a_1435_);
lean_dec(v_x_1419_);
return v___x_1437_;
}
}
else
{
lean_dec(v___x_1427_);
lean_dec(v_x_1419_);
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatPure___boxed(lean_object* v_x_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Fmt_fmtMCasesPatPure(v_x_1453_, v_a_1454_, v_a_1455_);
lean_dec_ref(v_a_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1(){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1463_ = l_Lean_Fmt_fmtAttribute;
v___x_1464_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatPure___closed__1));
v___x_1465_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___closed__1));
v___x_1466_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCasesPatPure___boxed), 3, 0);
v___x_1467_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1463_, v___x_1464_, v___x_1465_, v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1___boxed(lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1();
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatStateful(lean_object* v_x_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatStateful___closed__1));
lean_inc(v_x_1476_);
v___x_1480_ = l_Lean_Syntax_isOfKind(v_x_1476_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec(v_x_1476_);
v___x_1481_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_a_1478_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = l_Lean_Syntax_getArg(v_x_1476_, v___x_1483_);
v___x_1485_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_1484_);
v___x_1486_ = l_Lean_Syntax_isOfKind(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v___x_1484_);
lean_dec(v_x_1476_);
v___x_1487_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_a_1478_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; lean_object* v_boxTk_1490_; lean_object* v___x_1491_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v_boxTk_1490_ = l_Lean_Syntax_getArg(v_x_1476_, v___x_1489_);
lean_dec(v_x_1476_);
v___x_1491_ = l_Lean_Fmt_fmt(v_boxTk_1490_, v_a_1477_, v_a_1478_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
v_a_1493_ = lean_ctor_get(v___x_1491_, 1);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1491_, 2);
v___x_1494_ = l_Lean_Fmt_fmt(v___x_1484_, v_a_1477_, v_a_1493_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1505_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_a_1496_ = lean_ctor_get(v___x_1494_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1498_ = v___x_1494_;
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = 1;
v___x_1501_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_1492_, v_a_1495_, v___x_1500_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1501_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_a_1496_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
lean_dec(v_a_1492_);
return v___x_1494_;
}
}
else
{
lean_dec(v___x_1484_);
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatStateful___boxed(lean_object* v_x_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Fmt_fmtMCasesPatStateful(v_x_1506_, v_a_1507_, v_a_1508_);
lean_dec_ref(v_a_1507_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1(){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1516_ = l_Lean_Fmt_fmtAttribute;
v___x_1517_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatStateful___closed__1));
v___x_1518_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___closed__1));
v___x_1519_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCasesPatStateful___boxed), 3, 0);
v___x_1520_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1516_, v___x_1517_, v___x_1518_, v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1___boxed(lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1();
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatPureAbbrev(lean_object* v_x_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1));
lean_inc(v_x_1529_);
v___x_1533_ = l_Lean_Syntax_isOfKind(v_x_1529_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_x_1529_);
v___x_1534_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_a_1531_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = l_Lean_Syntax_getArg(v_x_1529_, v___x_1536_);
v___x_1538_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_1537_);
v___x_1539_ = l_Lean_Syntax_isOfKind(v___x_1537_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v___x_1537_);
lean_dec(v_x_1529_);
v___x_1540_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v_a_1531_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; lean_object* v_percentTk_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_unsigned_to_nat(0u);
v_percentTk_1543_ = l_Lean_Syntax_getArg(v_x_1529_, v___x_1542_);
lean_dec(v_x_1529_);
v___x_1544_ = l_Lean_Fmt_fmt(v_percentTk_1543_, v_a_1530_, v_a_1531_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
v_a_1546_ = lean_ctor_get(v___x_1544_, 1);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1544_, 2);
v___x_1547_ = l_Lean_Fmt_fmt(v___x_1537_, v_a_1530_, v_a_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1558_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_a_1549_ = lean_ctor_get(v___x_1547_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1551_ = v___x_1547_;
v_isShared_1552_ = v_isSharedCheck_1558_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1558_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1553_ = 1;
v___x_1554_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_1545_, v_a_1548_, v___x_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_a_1549_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_dec(v_a_1545_);
return v___x_1547_;
}
}
else
{
lean_dec(v___x_1537_);
return v___x_1544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatPureAbbrev___boxed(lean_object* v_x_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Fmt_fmtMCasesPatPureAbbrev(v_x_1559_, v_a_1560_, v_a_1561_);
lean_dec_ref(v_a_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1(){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1569_ = l_Lean_Fmt_fmtAttribute;
v___x_1570_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatPureAbbrev___closed__1));
v___x_1571_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___closed__1));
v___x_1572_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCasesPatPureAbbrev___boxed), 3, 0);
v___x_1573_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1569_, v___x_1570_, v___x_1571_, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1___boxed(lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1();
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatStatefulAbbrev(lean_object* v_x_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1));
lean_inc(v_x_1582_);
v___x_1586_ = l_Lean_Syntax_isOfKind(v_x_1582_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec(v_x_1582_);
v___x_1587_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v_a_1584_);
return v___x_1588_;
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = l_Lean_Syntax_getArg(v_x_1582_, v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_1590_);
v___x_1592_ = l_Lean_Syntax_isOfKind(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v___x_1590_);
lean_dec(v_x_1582_);
v___x_1593_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_a_1584_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; lean_object* v_hashTk_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v_hashTk_1596_ = l_Lean_Syntax_getArg(v_x_1582_, v___x_1595_);
lean_dec(v_x_1582_);
v___x_1597_ = l_Lean_Fmt_fmt(v_hashTk_1596_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v_a_1599_; lean_object* v___x_1600_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
v_a_1599_ = lean_ctor_get(v___x_1597_, 1);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1597_, 2);
v___x_1600_ = l_Lean_Fmt_fmt(v___x_1590_, v_a_1583_, v_a_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1611_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_a_1602_ = lean_ctor_get(v___x_1600_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1604_ = v___x_1600_;
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = 1;
v___x_1607_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_1598_, v_a_1601_, v___x_1606_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1607_);
v___x_1609_ = v___x_1604_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_a_1602_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
lean_dec(v_a_1598_);
return v___x_1600_;
}
}
else
{
lean_dec(v___x_1590_);
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___boxed(lean_object* v_x_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Fmt_fmtMCasesPatStatefulAbbrev(v_x_1612_, v_a_1613_, v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1(){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1622_ = l_Lean_Fmt_fmtAttribute;
v___x_1623_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___closed__1));
v___x_1624_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___closed__1));
v___x_1625_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCasesPatStatefulAbbrev___boxed), 3, 0);
v___x_1626_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1622_, v___x_1623_, v___x_1624_, v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1___boxed(lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1();
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCases(lean_object* v_x_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_Fmt_fmtMCases___closed__1));
lean_inc(v_x_1635_);
v___x_1639_ = l_Lean_Syntax_isOfKind(v_x_1635_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec(v_x_1635_);
v___x_1640_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v_a_1637_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = l_Lean_Syntax_getArg(v_x_1635_, v___x_1642_);
v___x_1644_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
lean_inc(v___x_1643_);
v___x_1645_ = l_Lean_Syntax_isOfKind(v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v___x_1643_);
lean_dec(v_x_1635_);
v___x_1646_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_ctor_set(v___x_1647_, 1, v_a_1637_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v_mcasesTk_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v_mcasesTk_1649_ = l_Lean_Syntax_getArg(v_x_1635_, v___x_1648_);
v___x_1650_ = l_Lean_Fmt_fmt(v_mcasesTk_1649_, v_a_1636_, v_a_1637_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v_a_1652_; lean_object* v___x_1653_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
v_a_1652_ = lean_ctor_get(v___x_1650_, 1);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1650_, 2);
v___x_1653_ = l_Lean_Fmt_fmt(v___x_1643_, v_a_1636_, v_a_1652_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v_a_1655_; lean_object* v___x_1656_; lean_object* v_withTk_1657_; lean_object* v___x_1658_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
v_a_1655_ = lean_ctor_get(v___x_1653_, 1);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1653_, 2);
v___x_1656_ = lean_unsigned_to_nat(2u);
v_withTk_1657_ = l_Lean_Syntax_getArg(v_x_1635_, v___x_1656_);
v___x_1658_ = l_Lean_Fmt_fmt(v_withTk_1657_, v_a_1636_, v_a_1655_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_a_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
v_a_1660_ = lean_ctor_get(v___x_1658_, 1);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1658_, 2);
v___x_1661_ = lean_unsigned_to_nat(3u);
v___x_1662_ = l_Lean_Syntax_getArg(v_x_1635_, v___x_1661_);
lean_dec(v_x_1635_);
v___x_1663_ = l_Lean_Fmt_fmt(v___x_1662_, v_a_1636_, v_a_1660_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1683_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_a_1665_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1667_ = v___x_1663_;
v_isShared_1668_ = v_isSharedCheck_1683_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1683_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1669_ = lean_mk_empty_array_with_capacity(v___x_1656_);
lean_inc_ref(v___x_1669_);
v___x_1670_ = lean_array_push(v___x_1669_, v_a_1651_);
v___x_1671_ = lean_array_push(v___x_1670_, v_a_1654_);
v___x_1672_ = 0;
v___x_1673_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1673_, 0, v___x_1645_);
lean_ctor_set_uint8(v___x_1673_, 1, v___x_1672_);
lean_ctor_set_uint8(v___x_1673_, 2, v___x_1672_);
lean_ctor_set_uint8(v___x_1673_, 3, v___x_1672_);
lean_inc_ref(v___x_1673_);
v___x_1674_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1671_, v___x_1673_);
v___x_1675_ = 0;
v___x_1676_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_a_1659_, v_a_1664_, v___x_1675_);
v___x_1677_ = lean_array_push(v___x_1669_, v___x_1674_);
v___x_1678_ = lean_array_push(v___x_1677_, v___x_1676_);
v___x_1679_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1678_, v___x_1673_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1679_);
v___x_1681_ = v___x_1667_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1665_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
else
{
lean_dec(v_a_1659_);
lean_dec(v_a_1654_);
lean_dec(v_a_1651_);
return v___x_1663_;
}
}
else
{
lean_dec(v_a_1654_);
lean_dec(v_a_1651_);
lean_dec(v_x_1635_);
return v___x_1658_;
}
}
else
{
lean_dec(v_a_1651_);
lean_dec(v_x_1635_);
return v___x_1653_;
}
}
else
{
lean_dec(v___x_1643_);
lean_dec(v_x_1635_);
return v___x_1650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMCases___boxed(lean_object* v_x_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Fmt_fmtMCases(v_x_1684_, v_a_1685_, v_a_1686_);
lean_dec_ref(v_a_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1(){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1694_ = l_Lean_Fmt_fmtAttribute;
v___x_1695_ = ((lean_object*)(l_Lean_Fmt_fmtMCases___closed__1));
v___x_1696_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___closed__1));
v___x_1697_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMCases___boxed), 3, 0);
v___x_1698_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1694_, v___x_1695_, v___x_1696_, v___x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1___boxed(lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1();
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatOne(lean_object* v_x_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatOne___closed__1));
lean_inc(v_x_1707_);
v___x_1711_ = l_Lean_Syntax_isOfKind(v_x_1707_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v_x_1707_);
v___x_1712_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v_a_1709_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = l_Lean_Syntax_getArg(v_x_1707_, v___x_1714_);
lean_dec(v_x_1707_);
v___x_1716_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_1715_);
v___x_1717_ = l_Lean_Syntax_isOfKind(v___x_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v___x_1715_);
v___x_1718_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
lean_ctor_set(v___x_1719_, 1, v_a_1709_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Fmt_fmt(v___x_1715_, v_a_1708_, v_a_1709_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatOne___boxed(lean_object* v_x_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Fmt_fmtMRefinePatOne(v_x_1721_, v_a_1722_, v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1(){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1731_ = l_Lean_Fmt_fmtAttribute;
v___x_1732_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatOne___closed__1));
v___x_1733_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___closed__1));
v___x_1734_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefinePatOne___boxed), 3, 0);
v___x_1735_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1731_, v___x_1732_, v___x_1733_, v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1___boxed(lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1();
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatTuple(lean_object* v_x_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatTuple___closed__1));
lean_inc(v_x_1750_);
v___x_1754_ = l_Lean_Syntax_isOfKind(v_x_1750_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_x_1750_);
v___x_1755_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v_a_1752_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = l_Lean_Syntax_getArg(v_x_1750_, v___x_1757_);
v___x_1759_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatTuple___closed__3));
lean_inc(v___x_1758_);
v___x_1760_ = l_Lean_Syntax_isOfKind(v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v___x_1758_);
lean_dec(v_x_1750_);
v___x_1761_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v_a_1752_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; lean_object* v_lbTk_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v_lbTk_1764_ = l_Lean_Syntax_getArg(v_x_1750_, v___x_1763_);
v___x_1765_ = l_Lean_Fmt_fmt(v_lbTk_1764_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v_pats_1769_; lean_object* v___x_1770_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
v_a_1767_ = lean_ctor_get(v___x_1765_, 1);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1765_, 2);
v___x_1768_ = l_Lean_Syntax_getArg(v___x_1758_, v___x_1763_);
lean_dec(v___x_1758_);
v_pats_1769_ = l_Lean_Syntax_getArgs(v___x_1768_);
lean_dec(v___x_1768_);
v___x_1770_ = l_Lean_Fmt_fmtTSepArray___redArg(v_pats_1769_, v_a_1751_, v_a_1767_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v_rbTk_1774_; lean_object* v___x_1775_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
v_a_1772_ = lean_ctor_get(v___x_1770_, 1);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1770_, 2);
v___x_1773_ = lean_unsigned_to_nat(2u);
v_rbTk_1774_ = l_Lean_Syntax_getArg(v_x_1750_, v___x_1773_);
lean_dec(v_x_1750_);
v___x_1775_ = l_Lean_Fmt_fmt(v_rbTk_1774_, v_a_1751_, v_a_1772_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1786_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_a_1777_ = lean_ctor_get(v___x_1775_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1779_ = v___x_1775_;
v_isShared_1780_ = v_isSharedCheck_1786_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1786_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1781_ = ((lean_object*)(l_Lean_Fmt_fmtMExists___closed__2));
v___x_1782_ = l_Lean_Fmt_Layouts_tuple(v___x_1781_, v_a_1766_, v_a_1771_, v_a_1776_);
lean_dec(v_a_1771_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1782_);
v___x_1784_ = v___x_1779_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_a_1777_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_dec(v_a_1771_);
lean_dec(v_a_1766_);
return v___x_1775_;
}
}
else
{
lean_object* v_a_1787_; lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_a_1766_);
lean_dec(v_x_1750_);
v_a_1787_ = lean_ctor_get(v___x_1770_, 0);
v_a_1788_ = lean_ctor_get(v___x_1770_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1770_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_inc(v_a_1787_);
lean_dec(v___x_1770_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1787_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_dec(v___x_1758_);
lean_dec(v_x_1750_);
return v___x_1765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatTuple___boxed(lean_object* v_x_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Fmt_fmtMRefinePatTuple(v_x_1796_, v_a_1797_, v_a_1798_);
lean_dec_ref(v_a_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1(){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1806_ = l_Lean_Fmt_fmtAttribute;
v___x_1807_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatTuple___closed__1));
v___x_1808_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___closed__1));
v___x_1809_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefinePatTuple___boxed), 3, 0);
v___x_1810_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1806_, v___x_1807_, v___x_1808_, v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1___boxed(lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1();
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatParen(lean_object* v_x_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatParen___closed__1));
lean_inc(v_x_1819_);
v___x_1823_ = l_Lean_Syntax_isOfKind(v_x_1819_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v_x_1819_);
v___x_1824_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v_a_1821_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v_lbTk_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_unsigned_to_nat(0u);
v_lbTk_1827_ = l_Lean_Syntax_getArg(v_x_1819_, v___x_1826_);
v___x_1828_ = l_Lean_Fmt_fmt(v_lbTk_1827_, v_a_1820_, v_a_1821_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v_a_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
v_a_1830_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1828_, 2);
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = l_Lean_Syntax_getArg(v_x_1819_, v___x_1831_);
v___x_1833_ = l_Lean_Fmt_fmt(v___x_1832_, v_a_1820_, v_a_1830_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v_a_1835_; lean_object* v___x_1836_; lean_object* v_rbTk_1837_; lean_object* v___x_1838_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
v_a_1835_ = lean_ctor_get(v___x_1833_, 1);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1833_, 2);
v___x_1836_ = lean_unsigned_to_nat(2u);
v_rbTk_1837_ = l_Lean_Syntax_getArg(v_x_1819_, v___x_1836_);
lean_dec(v_x_1819_);
v___x_1838_ = l_Lean_Fmt_fmt(v_rbTk_1837_, v_a_1820_, v_a_1835_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1848_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_a_1840_ = lean_ctor_get(v___x_1838_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1842_ = v___x_1838_;
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1844_ = l_Lean_Fmt_Layouts_parens(v_a_1829_, v_a_1834_, v_a_1839_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_a_1840_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
lean_dec(v_a_1834_);
lean_dec(v_a_1829_);
return v___x_1838_;
}
}
else
{
lean_dec(v_a_1829_);
lean_dec(v_x_1819_);
return v___x_1833_;
}
}
else
{
lean_dec(v_x_1819_);
return v___x_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatParen___boxed(lean_object* v_x_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Fmt_fmtMRefinePatParen(v_x_1849_, v_a_1850_, v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1(){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1859_ = l_Lean_Fmt_fmtAttribute;
v___x_1860_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatParen___closed__1));
v___x_1861_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___closed__1));
v___x_1862_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefinePatParen___boxed), 3, 0);
v___x_1863_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1859_, v___x_1860_, v___x_1861_, v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1___boxed(lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1();
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatPure(lean_object* v_x_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatPure___closed__1));
lean_inc(v_x_1872_);
v___x_1876_ = l_Lean_Syntax_isOfKind(v_x_1872_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v_x_1872_);
v___x_1877_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_a_1874_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; lean_object* v_lbTk_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_unsigned_to_nat(0u);
v_lbTk_1880_ = l_Lean_Syntax_getArg(v_x_1872_, v___x_1879_);
v___x_1881_ = l_Lean_Fmt_fmt(v_lbTk_1880_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v_a_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
v_a_1883_ = lean_ctor_get(v___x_1881_, 1);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1881_, 2);
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = l_Lean_Syntax_getArg(v_x_1872_, v___x_1884_);
v___x_1886_ = l_Lean_Fmt_fmt(v___x_1885_, v_a_1873_, v_a_1883_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v_rbTk_1890_; lean_object* v___x_1891_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
v_a_1888_ = lean_ctor_get(v___x_1886_, 1);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1886_, 2);
v___x_1889_ = lean_unsigned_to_nat(2u);
v_rbTk_1890_ = l_Lean_Syntax_getArg(v_x_1872_, v___x_1889_);
lean_dec(v_x_1872_);
v___x_1891_ = l_Lean_Fmt_fmt(v_rbTk_1890_, v_a_1873_, v_a_1888_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1901_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_a_1893_ = lean_ctor_get(v___x_1891_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1895_ = v___x_1891_;
v_isShared_1896_ = v_isSharedCheck_1901_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1901_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = l_Lean_Fmt_Layouts_parens(v_a_1882_, v_a_1887_, v_a_1892_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1897_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_a_1893_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
else
{
lean_dec(v_a_1887_);
lean_dec(v_a_1882_);
return v___x_1891_;
}
}
else
{
lean_dec(v_a_1882_);
lean_dec(v_x_1872_);
return v___x_1886_;
}
}
else
{
lean_dec(v_x_1872_);
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatPure___boxed(lean_object* v_x_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Fmt_fmtMRefinePatPure(v_x_1902_, v_a_1903_, v_a_1904_);
lean_dec_ref(v_a_1903_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1(){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1912_ = l_Lean_Fmt_fmtAttribute;
v___x_1913_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatPure___closed__1));
v___x_1914_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___closed__1));
v___x_1915_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefinePatPure___boxed), 3, 0);
v___x_1916_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1912_, v___x_1913_, v___x_1914_, v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1___boxed(lean_object* v_a_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1();
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatStateful(lean_object* v_x_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatStateful___closed__1));
lean_inc(v_x_1925_);
v___x_1929_ = l_Lean_Syntax_isOfKind(v_x_1925_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_dec(v_x_1925_);
v___x_1930_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v_a_1927_);
return v___x_1931_;
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1932_ = lean_unsigned_to_nat(1u);
v___x_1933_ = l_Lean_Syntax_getArg(v_x_1925_, v___x_1932_);
v___x_1934_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_1933_);
v___x_1935_ = l_Lean_Syntax_isOfKind(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v___x_1933_);
lean_dec(v_x_1925_);
v___x_1936_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v_a_1927_);
return v___x_1937_;
}
else
{
lean_object* v___x_1938_; lean_object* v_boxTk_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_unsigned_to_nat(0u);
v_boxTk_1939_ = l_Lean_Syntax_getArg(v_x_1925_, v___x_1938_);
lean_dec(v_x_1925_);
v___x_1940_ = l_Lean_Fmt_fmt(v_boxTk_1939_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_a_1942_; lean_object* v___x_1943_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
v_a_1942_ = lean_ctor_get(v___x_1940_, 1);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1940_, 2);
v___x_1943_ = l_Lean_Fmt_fmt(v___x_1933_, v_a_1926_, v_a_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1954_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_a_1945_ = lean_ctor_get(v___x_1943_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1947_ = v___x_1943_;
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
uint8_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1949_ = 1;
v___x_1950_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_1941_, v_a_1944_, v___x_1949_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1950_);
v___x_1952_ = v___x_1947_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_a_1945_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_dec(v_a_1941_);
return v___x_1943_;
}
}
else
{
lean_dec(v___x_1933_);
return v___x_1940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatStateful___boxed(lean_object* v_x_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Fmt_fmtMRefinePatStateful(v_x_1955_, v_a_1956_, v_a_1957_);
lean_dec_ref(v_a_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1(){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1965_ = l_Lean_Fmt_fmtAttribute;
v___x_1966_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatStateful___closed__1));
v___x_1967_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___closed__1));
v___x_1968_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefinePatStateful___boxed), 3, 0);
v___x_1969_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1965_, v___x_1966_, v___x_1967_, v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1___boxed(lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1();
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatHole(lean_object* v_x_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatHole___closed__1));
lean_inc(v_x_1978_);
v___x_1982_ = l_Lean_Syntax_isOfKind(v_x_1978_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_dec(v_x_1978_);
v___x_1983_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v_a_1980_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = l_Lean_Syntax_getArg(v_x_1978_, v___x_1985_);
v___x_1987_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_1986_);
v___x_1988_ = l_Lean_Syntax_isOfKind(v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec(v___x_1986_);
lean_dec(v_x_1978_);
v___x_1989_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_a_1980_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v_questionTk_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_unsigned_to_nat(0u);
v_questionTk_1992_ = l_Lean_Syntax_getArg(v_x_1978_, v___x_1991_);
lean_dec(v_x_1978_);
v___x_1993_ = l_Lean_Fmt_fmt(v_questionTk_1992_, v_a_1979_, v_a_1980_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v_a_1995_; lean_object* v___x_1996_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
v_a_1995_ = lean_ctor_get(v___x_1993_, 1);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1993_, 2);
v___x_1996_ = l_Lean_Fmt_fmt(v___x_1986_, v_a_1979_, v_a_1995_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2007_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_a_1998_ = lean_ctor_get(v___x_1996_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2000_ = v___x_1996_;
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = 1;
v___x_2003_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_1994_, v_a_1997_, v___x_2002_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_a_1998_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_dec(v_a_1994_);
return v___x_1996_;
}
}
else
{
lean_dec(v___x_1986_);
return v___x_1993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatHole___boxed(lean_object* v_x_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Fmt_fmtMRefinePatHole(v_x_2008_, v_a_2009_, v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1(){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2018_ = l_Lean_Fmt_fmtAttribute;
v___x_2019_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatHole___closed__1));
v___x_2020_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___closed__1));
v___x_2021_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefinePatHole___boxed), 3, 0);
v___x_2022_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2018_, v___x_2019_, v___x_2020_, v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1___boxed(lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1();
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatPureAbbrev(lean_object* v_x_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1));
lean_inc(v_x_2031_);
v___x_2035_ = l_Lean_Syntax_isOfKind(v_x_2031_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec(v_x_2031_);
v___x_2036_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v_a_2033_);
return v___x_2037_;
}
else
{
lean_object* v___x_2038_; lean_object* v_percentTk_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_unsigned_to_nat(0u);
v_percentTk_2039_ = l_Lean_Syntax_getArg(v_x_2031_, v___x_2038_);
v___x_2040_ = l_Lean_Fmt_fmt(v_percentTk_2039_, v_a_2032_, v_a_2033_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
v_a_2042_ = lean_ctor_get(v___x_2040_, 1);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2040_, 2);
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = l_Lean_Syntax_getArg(v_x_2031_, v___x_2043_);
lean_dec(v_x_2031_);
v___x_2045_ = l_Lean_Fmt_fmt(v___x_2044_, v_a_2032_, v_a_2042_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2056_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_a_2047_ = lean_ctor_get(v___x_2045_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2049_ = v___x_2045_;
v_isShared_2050_ = v_isSharedCheck_2056_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2056_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
uint8_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2051_ = 1;
v___x_2052_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_2041_, v_a_2046_, v___x_2051_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2052_);
v___x_2054_ = v___x_2049_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_a_2047_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_dec(v_a_2041_);
return v___x_2045_;
}
}
else
{
lean_dec(v_x_2031_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatPureAbbrev___boxed(lean_object* v_x_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Fmt_fmtMRefinePatPureAbbrev(v_x_2057_, v_a_2058_, v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1(){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2067_ = l_Lean_Fmt_fmtAttribute;
v___x_2068_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatPureAbbrev___closed__1));
v___x_2069_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___closed__1));
v___x_2070_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefinePatPureAbbrev___boxed), 3, 0);
v___x_2071_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2067_, v___x_2068_, v___x_2069_, v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1___boxed(lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1();
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatStatefulAbbrev(lean_object* v_x_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1));
lean_inc(v_x_2080_);
v___x_2084_ = l_Lean_Syntax_isOfKind(v_x_2080_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec(v_x_2080_);
v___x_2085_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v_a_2082_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2087_ = lean_unsigned_to_nat(1u);
v___x_2088_ = l_Lean_Syntax_getArg(v_x_2080_, v___x_2087_);
v___x_2089_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_2088_);
v___x_2090_ = l_Lean_Syntax_isOfKind(v___x_2088_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec(v___x_2088_);
lean_dec(v_x_2080_);
v___x_2091_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_a_2082_);
return v___x_2092_;
}
else
{
lean_object* v___x_2093_; lean_object* v_hashTk_2094_; lean_object* v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(0u);
v_hashTk_2094_ = l_Lean_Syntax_getArg(v_x_2080_, v___x_2093_);
lean_dec(v_x_2080_);
v___x_2095_ = l_Lean_Fmt_fmt(v_hashTk_2094_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
v_a_2097_ = lean_ctor_get(v___x_2095_, 1);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2095_, 2);
v___x_2098_ = l_Lean_Fmt_fmt(v___x_2088_, v_a_2081_, v_a_2097_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2109_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_a_2100_ = lean_ctor_get(v___x_2098_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2102_ = v___x_2098_;
v_isShared_2103_ = v_isSharedCheck_2109_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2109_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2104_ = 1;
v___x_2105_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_2096_, v_a_2099_, v___x_2104_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2105_);
v___x_2107_ = v___x_2102_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_a_2100_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
else
{
lean_dec(v_a_2096_);
return v___x_2098_;
}
}
else
{
lean_dec(v___x_2088_);
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___boxed(lean_object* v_x_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Fmt_fmtMRefinePatStatefulAbbrev(v_x_2110_, v_a_2111_, v_a_2112_);
lean_dec_ref(v_a_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1(){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2120_ = l_Lean_Fmt_fmtAttribute;
v___x_2121_ = ((lean_object*)(l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___closed__1));
v___x_2122_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___closed__1));
v___x_2123_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRefinePatStatefulAbbrev___boxed), 3, 0);
v___x_2124_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1___boxed(lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1();
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntroPatCases(lean_object* v_x_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Lean_Fmt_fmtMIntroPatCases___closed__1));
lean_inc(v_x_2133_);
v___x_2137_ = l_Lean_Syntax_isOfKind(v_x_2133_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec(v_x_2133_);
v___x_2138_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v_a_2135_);
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_unsigned_to_nat(0u);
v___x_2141_ = l_Lean_Syntax_getArg(v_x_2133_, v___x_2140_);
lean_dec(v_x_2133_);
v___x_2142_ = l_Lean_Fmt_fmt(v___x_2141_, v_a_2134_, v_a_2135_);
return v___x_2142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntroPatCases___boxed(lean_object* v_x_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Fmt_fmtMIntroPatCases(v_x_2143_, v_a_2144_, v_a_2145_);
lean_dec_ref(v_a_2144_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1(){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2153_ = l_Lean_Fmt_fmtAttribute;
v___x_2154_ = ((lean_object*)(l_Lean_Fmt_fmtMIntroPatCases___closed__1));
v___x_2155_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___closed__1));
v___x_2156_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMIntroPatCases___boxed), 3, 0);
v___x_2157_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2153_, v___x_2154_, v___x_2155_, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1___boxed(lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1();
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntroPatForall(lean_object* v_x_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_Fmt_fmtMIntroPatForall___closed__1));
lean_inc(v_x_2166_);
v___x_2170_ = l_Lean_Syntax_isOfKind(v_x_2166_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec(v_x_2166_);
v___x_2171_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v_a_2168_);
return v___x_2172_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = l_Lean_Syntax_getArg(v_x_2166_, v___x_2173_);
v___x_2175_ = ((lean_object*)(l_Lean_Fmt_fmtMCasesPatOne___closed__3));
lean_inc(v___x_2174_);
v___x_2176_ = l_Lean_Syntax_isOfKind(v___x_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec(v___x_2174_);
lean_dec(v_x_2166_);
v___x_2177_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v_a_2168_);
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; lean_object* v_forallTk_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v_forallTk_2180_ = l_Lean_Syntax_getArg(v_x_2166_, v___x_2179_);
lean_dec(v_x_2166_);
v___x_2181_ = l_Lean_Fmt_fmt(v_forallTk_2180_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
v_a_2183_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2181_, 2);
v___x_2184_ = l_Lean_Fmt_fmt(v___x_2174_, v_a_2167_, v_a_2183_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2195_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_a_2186_ = lean_ctor_get(v___x_2184_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2188_ = v___x_2184_;
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2190_ = 2;
v___x_2191_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_2182_, v_a_2185_, v___x_2190_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2191_);
v___x_2193_ = v___x_2188_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_a_2186_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
else
{
lean_dec(v_a_2182_);
return v___x_2184_;
}
}
else
{
lean_dec(v___x_2174_);
return v___x_2181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMIntroPatForall___boxed(lean_object* v_x_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Fmt_fmtMIntroPatForall(v_x_2196_, v_a_2197_, v_a_2198_);
lean_dec_ref(v_a_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1(){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2206_ = l_Lean_Fmt_fmtAttribute;
v___x_2207_ = ((lean_object*)(l_Lean_Fmt_fmtMIntroPatForall___closed__1));
v___x_2208_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___closed__1));
v___x_2209_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMIntroPatForall___boxed), 3, 0);
v___x_2210_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2206_, v___x_2207_, v___x_2208_, v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1___boxed(lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1();
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevertPatOne(lean_object* v_x_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_Lean_Fmt_fmtMRevertPatOne___closed__1));
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
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = l_Lean_Syntax_getArg(v_x_2219_, v___x_2226_);
lean_dec(v_x_2219_);
v___x_2228_ = ((lean_object*)(l_Lean_Fmt_fmtMClear___closed__6));
lean_inc(v___x_2227_);
v___x_2229_ = l_Lean_Syntax_isOfKind(v___x_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v___x_2227_);
v___x_2230_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v_a_2221_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Fmt_fmt(v___x_2227_, v_a_2220_, v_a_2221_);
return v___x_2232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevertPatOne___boxed(lean_object* v_x_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_Fmt_fmtMRevertPatOne(v_x_2233_, v_a_2234_, v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1(){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2243_ = l_Lean_Fmt_fmtAttribute;
v___x_2244_ = ((lean_object*)(l_Lean_Fmt_fmtMRevertPatOne___closed__1));
v___x_2245_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___closed__1));
v___x_2246_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRevertPatOne___boxed), 3, 0);
v___x_2247_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2243_, v___x_2244_, v___x_2245_, v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1___boxed(lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1();
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevertPatForall(lean_object* v_x_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2279_ = ((lean_object*)(l_Lean_Fmt_fmtMRevertPatForall___closed__1));
lean_inc(v_x_2259_);
v___x_2280_ = l_Lean_Syntax_isOfKind(v_x_2259_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec(v_x_2259_);
v___x_2281_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v_a_2261_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; lean_object* v_forallTk_2284_; lean_object* v_n_x3f_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2283_ = lean_unsigned_to_nat(0u);
v_forallTk_2284_ = l_Lean_Syntax_getArg(v_x_2259_, v___x_2283_);
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = l_Lean_Syntax_getArg(v_x_2259_, v___x_2303_);
lean_dec(v_x_2259_);
v___x_2305_ = l_Lean_Syntax_isNone(v___x_2304_);
if (v___x_2305_ == 0)
{
uint8_t v___x_2306_; 
lean_inc(v___x_2304_);
v___x_2306_ = l_Lean_Syntax_matchesNull(v___x_2304_, v___x_2303_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v___x_2304_);
lean_dec(v_forallTk_2284_);
v___x_2307_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v_a_2261_);
return v___x_2308_;
}
else
{
lean_object* v_n_x3f_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_n_x3f_2309_ = l_Lean_Syntax_getArg(v___x_2304_, v___x_2283_);
lean_dec(v___x_2304_);
v___x_2310_ = ((lean_object*)(l_Lean_Fmt_fmtMRevertPatForall___closed__3));
lean_inc(v_n_x3f_2309_);
v___x_2311_ = l_Lean_Syntax_isOfKind(v_n_x3f_2309_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_dec(v_n_x3f_2309_);
lean_dec(v_forallTk_2284_);
v___x_2312_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v_a_2261_);
return v___x_2313_;
}
else
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_n_x3f_2309_);
v_n_x3f_2286_ = v___x_2314_;
v___y_2287_ = v_a_2260_;
v___y_2288_ = v_a_2261_;
goto v___jp_2285_;
}
}
}
else
{
lean_object* v___x_2315_; 
lean_dec(v___x_2304_);
v___x_2315_ = lean_box(0);
v_n_x3f_2286_ = v___x_2315_;
v___y_2287_ = v_a_2260_;
v___y_2288_ = v_a_2261_;
goto v___jp_2285_;
}
v___jp_2285_:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Fmt_fmt(v_forallTk_2284_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2289_) == 0)
{
if (lean_obj_tag(v_n_x3f_2286_) == 0)
{
lean_object* v_a_2290_; lean_object* v_a_2291_; lean_object* v___x_2292_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
v_a_2291_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2289_, 2);
v___x_2292_ = lean_box(0);
v___y_2263_ = v_a_2290_;
v___y_2264_ = v___y_2287_;
v___y_2265_ = v_a_2291_;
v___y_2266_ = v___x_2292_;
goto v___jp_2262_;
}
else
{
lean_object* v_a_2293_; lean_object* v_a_2294_; lean_object* v_val_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
v_a_2293_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2293_);
v_a_2294_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2289_, 2);
v_val_2295_ = lean_ctor_get(v_n_x3f_2286_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_n_x3f_2286_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v_n_x3f_2286_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_val_2295_);
lean_dec(v_n_x3f_2286_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_val_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
v___y_2263_ = v_a_2293_;
v___y_2264_ = v___y_2287_;
v___y_2265_ = v_a_2294_;
v___y_2266_ = v___x_2300_;
goto v___jp_2262_;
}
}
}
}
else
{
lean_dec(v_n_x3f_2286_);
return v___x_2289_;
}
}
}
v___jp_2262_:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Fmt_fmt_x3f(v___y_2266_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2278_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_a_2269_ = lean_ctor_get(v___x_2267_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2271_ = v___x_2267_;
v_isShared_2272_ = v_isSharedCheck_2278_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2278_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = 2;
v___x_2274_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_2263_, v_a_2268_, v___x_2273_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2274_);
v___x_2276_ = v___x_2271_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_a_2269_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
else
{
lean_dec_ref(v___y_2263_);
return v___x_2267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMRevertPatForall___boxed(lean_object* v_x_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Fmt_fmtMRevertPatForall(v_x_2316_, v_a_2317_, v_a_2318_);
lean_dec_ref(v_a_2317_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1(){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2326_ = l_Lean_Fmt_fmtAttribute;
v___x_2327_ = ((lean_object*)(l_Lean_Fmt_fmtMRevertPatForall___closed__1));
v___x_2328_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___closed__1));
v___x_2329_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMRevertPatForall___boxed), 3, 0);
v___x_2330_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2326_, v___x_2327_, v___x_2328_, v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1___boxed(lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1();
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCAlt(lean_object* v_x_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = ((lean_object*)(l_Lean_Fmt_fmtVCAlt___closed__1));
lean_inc(v_x_2345_);
v___x_2349_ = l_Lean_Syntax_isOfKind(v_x_2345_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec(v_x_2345_);
v___x_2350_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v_a_2347_);
return v___x_2351_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2352_ = lean_unsigned_to_nat(3u);
v___x_2353_ = l_Lean_Syntax_getArg(v_x_2345_, v___x_2352_);
v___x_2354_ = ((lean_object*)(l_Lean_Fmt_fmtVCAlt___closed__3));
lean_inc(v___x_2353_);
v___x_2355_ = l_Lean_Syntax_isOfKind(v___x_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_dec(v___x_2353_);
lean_dec(v_x_2345_);
v___x_2356_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v_a_2347_);
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; lean_object* v_pipeTk_2359_; lean_object* v___x_2360_; 
v___x_2358_ = lean_unsigned_to_nat(0u);
v_pipeTk_2359_ = l_Lean_Syntax_getArg(v_x_2345_, v___x_2358_);
v___x_2360_ = l_Lean_Fmt_fmt(v_pipeTk_2359_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v_args_2365_; lean_object* v___x_2366_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
v_a_2362_ = lean_ctor_get(v___x_2360_, 1);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2360_, 2);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = l_Lean_Syntax_getArg(v_x_2345_, v___x_2363_);
v_args_2365_ = l_Lean_Syntax_getArgs(v___x_2364_);
lean_dec(v___x_2364_);
v___x_2366_ = l_Lean_Fmt_fmtTSepArray___redArg(v_args_2365_, v_a_2346_, v_a_2362_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v_a_2368_; lean_object* v___x_2369_; lean_object* v_arrowTk_2370_; lean_object* v___x_2371_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
v_a_2368_ = lean_ctor_get(v___x_2366_, 1);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2366_, 2);
v___x_2369_ = lean_unsigned_to_nat(2u);
v_arrowTk_2370_ = l_Lean_Syntax_getArg(v_x_2345_, v___x_2369_);
lean_dec(v_x_2345_);
v___x_2371_ = l_Lean_Fmt_fmt(v_arrowTk_2370_, v_a_2346_, v_a_2368_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v_a_2373_; lean_object* v___x_2374_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
v_a_2373_ = lean_ctor_get(v___x_2371_, 1);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2371_, 2);
v___x_2374_ = l_Lean_Fmt_fmt(v___x_2353_, v_a_2346_, v_a_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2386_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_a_2376_ = lean_ctor_get(v___x_2374_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2378_ = v___x_2374_;
v_isShared_2379_ = v_isSharedCheck_2386_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2386_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2380_ = l_Lean_Fmt_joinAltPats___redArg(v_a_2361_, v_a_2367_);
lean_dec(v_a_2367_);
v___x_2381_ = 0;
v___x_2382_ = l_Lean_Fmt_Layouts_alt(v___x_2380_, v_a_2372_, v_a_2375_, v___x_2381_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2382_);
v___x_2384_ = v___x_2378_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2376_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_a_2372_);
lean_dec(v_a_2367_);
lean_dec(v_a_2361_);
v_a_2387_ = lean_ctor_get(v___x_2374_, 0);
v_a_2388_ = lean_ctor_get(v___x_2374_, 1);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2374_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_inc(v_a_2387_);
lean_dec(v___x_2374_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2387_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_a_2367_);
lean_dec(v_a_2361_);
lean_dec(v___x_2353_);
v_a_2396_ = lean_ctor_get(v___x_2371_, 0);
v_a_2397_ = lean_ctor_get(v___x_2371_, 1);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2371_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_inc(v_a_2396_);
lean_dec(v___x_2371_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2396_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_a_2361_);
lean_dec(v___x_2353_);
lean_dec(v_x_2345_);
v_a_2405_ = lean_ctor_get(v___x_2366_, 0);
v_a_2406_ = lean_ctor_get(v___x_2366_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2366_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_inc(v_a_2405_);
lean_dec(v___x_2366_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2405_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v___x_2353_);
lean_dec(v_x_2345_);
v_a_2414_ = lean_ctor_get(v___x_2360_, 0);
v_a_2415_ = lean_ctor_get(v___x_2360_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2360_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_inc(v_a_2414_);
lean_dec(v___x_2360_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2414_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCAlt___boxed(lean_object* v_x_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Fmt_fmtVCAlt(v_x_2423_, v_a_2424_, v_a_2425_);
lean_dec_ref(v_a_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__0(size_t v_sz_2427_, size_t v_i_2428_, lean_object* v_bs_2429_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_usize_dec_lt(v_i_2428_, v_sz_2427_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_bs_2429_);
return v___x_2431_;
}
else
{
lean_object* v_v_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v_v_2432_ = lean_array_uget(v_bs_2429_, v_i_2428_);
v___x_2433_ = ((lean_object*)(l_Lean_Fmt_fmtVCAlt___closed__1));
lean_inc(v_v_2432_);
v___x_2434_ = l_Lean_Syntax_isOfKind(v_v_2432_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; 
lean_dec(v_v_2432_);
lean_dec_ref(v_bs_2429_);
v___x_2435_ = lean_box(0);
return v___x_2435_;
}
else
{
lean_object* v___x_2436_; lean_object* v_bs_x27_2437_; size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2436_ = lean_unsigned_to_nat(0u);
v_bs_x27_2437_ = lean_array_uset(v_bs_2429_, v_i_2428_, v___x_2436_);
v___x_2438_ = ((size_t)1ULL);
v___x_2439_ = lean_usize_add(v_i_2428_, v___x_2438_);
v___x_2440_ = lean_array_uset(v_bs_x27_2437_, v_i_2428_, v_v_2432_);
v_i_2428_ = v___x_2439_;
v_bs_2429_ = v___x_2440_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__0___boxed(lean_object* v_sz_2442_, lean_object* v_i_2443_, lean_object* v_bs_2444_){
_start:
{
size_t v_sz_boxed_2445_; size_t v_i_boxed_2446_; lean_object* v_res_2447_; 
v_sz_boxed_2445_ = lean_unbox_usize(v_sz_2442_);
lean_dec(v_sz_2442_);
v_i_boxed_2446_ = lean_unbox_usize(v_i_2443_);
lean_dec(v_i_2443_);
v_res_2447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__0(v_sz_boxed_2445_, v_i_boxed_2446_, v_bs_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__1(size_t v_sz_2448_, size_t v_i_2449_, lean_object* v_bs_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
uint8_t v___x_2453_; 
v___x_2453_ = lean_usize_dec_lt(v_i_2449_, v_sz_2448_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_bs_2450_);
lean_ctor_set(v___x_2454_, 1, v___y_2452_);
return v___x_2454_;
}
else
{
lean_object* v_v_2455_; lean_object* v___x_2456_; 
v_v_2455_ = lean_array_uget_borrowed(v_bs_2450_, v_i_2449_);
lean_inc(v_v_2455_);
v___x_2456_ = l_Lean_Fmt_fmtVCAlt(v_v_2455_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v_bs_x27_2460_; size_t v___x_2461_; size_t v___x_2462_; lean_object* v___x_2463_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
v_a_2458_ = lean_ctor_get(v___x_2456_, 1);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2456_, 2);
v___x_2459_ = lean_unsigned_to_nat(0u);
v_bs_x27_2460_ = lean_array_uset(v_bs_2450_, v_i_2449_, v___x_2459_);
v___x_2461_ = ((size_t)1ULL);
v___x_2462_ = lean_usize_add(v_i_2449_, v___x_2461_);
v___x_2463_ = lean_array_uset(v_bs_x27_2460_, v_i_2449_, v_a_2457_);
v_i_2449_ = v___x_2462_;
v_bs_2450_ = v___x_2463_;
v___y_2452_ = v_a_2458_;
goto _start;
}
else
{
lean_object* v_a_2465_; lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_bs_2450_);
v_a_2465_ = lean_ctor_get(v___x_2456_, 0);
v_a_2466_ = lean_ctor_get(v___x_2456_, 1);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2456_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_inc(v_a_2465_);
lean_dec(v___x_2456_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2465_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__1___boxed(lean_object* v_sz_2474_, lean_object* v_i_2475_, lean_object* v_bs_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
size_t v_sz_boxed_2479_; size_t v_i_boxed_2480_; lean_object* v_res_2481_; 
v_sz_boxed_2479_ = lean_unbox_usize(v_sz_2474_);
lean_dec(v_sz_2474_);
v_i_boxed_2480_ = lean_unbox_usize(v_i_2475_);
lean_dec(v_i_2475_);
v_res_2481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__1(v_sz_boxed_2479_, v_i_boxed_2480_, v_bs_2476_, v___y_2477_, v___y_2478_);
lean_dec_ref(v___y_2477_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCAlts(lean_object* v_x_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; size_t v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; 
v___x_2491_ = ((lean_object*)(l_Lean_Fmt_fmtVCAlts___closed__1));
lean_inc(v_x_2488_);
v___x_2492_ = l_Lean_Syntax_isOfKind(v_x_2488_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_dec(v_x_2488_);
v___x_2532_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v_a_2490_);
return v___x_2533_;
}
else
{
lean_object* v___x_2534_; lean_object* v_withTk_2535_; lean_object* v_tac_x3f_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2534_ = lean_unsigned_to_nat(0u);
v_withTk_2535_ = l_Lean_Syntax_getArg(v_x_2488_, v___x_2534_);
v___x_2563_ = lean_unsigned_to_nat(1u);
v___x_2564_ = l_Lean_Syntax_getArg(v_x_2488_, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_isNone(v___x_2564_);
if (v___x_2565_ == 0)
{
uint8_t v___x_2566_; 
lean_inc(v___x_2564_);
v___x_2566_ = l_Lean_Syntax_matchesNull(v___x_2564_, v___x_2563_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec(v___x_2564_);
lean_dec(v_withTk_2535_);
lean_dec(v_x_2488_);
v___x_2567_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v_a_2490_);
return v___x_2568_;
}
else
{
lean_object* v_tac_x3f_2569_; lean_object* v___x_2570_; 
v_tac_x3f_2569_ = l_Lean_Syntax_getArg(v___x_2564_, v___x_2534_);
lean_dec(v___x_2564_);
v___x_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_tac_x3f_2569_);
v_tac_x3f_2537_ = v___x_2570_;
v___y_2538_ = v_a_2489_;
v___y_2539_ = v_a_2490_;
goto v___jp_2536_;
}
}
else
{
lean_object* v___x_2571_; 
lean_dec(v___x_2564_);
v___x_2571_ = lean_box(0);
v_tac_x3f_2537_ = v___x_2571_;
v___y_2538_ = v_a_2489_;
v___y_2539_ = v_a_2490_;
goto v___jp_2536_;
}
v___jp_2536_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; size_t v_sz_2543_; size_t v___x_2544_; lean_object* v___x_2545_; 
v___x_2540_ = lean_unsigned_to_nat(2u);
v___x_2541_ = l_Lean_Syntax_getArg(v_x_2488_, v___x_2540_);
lean_dec(v_x_2488_);
v___x_2542_ = l_Lean_Syntax_getArgs(v___x_2541_);
lean_dec(v___x_2541_);
v_sz_2543_ = lean_array_size(v___x_2542_);
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__0(v_sz_2543_, v___x_2544_, v___x_2542_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec(v_tac_x3f_2537_);
lean_dec(v_withTk_2535_);
v___x_2546_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
lean_ctor_set(v___x_2547_, 1, v___y_2539_);
return v___x_2547_;
}
else
{
lean_object* v_val_2548_; lean_object* v___x_2549_; 
v_val_2548_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2549_ = l_Lean_Fmt_fmt(v_withTk_2535_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2549_) == 0)
{
if (lean_obj_tag(v_tac_x3f_2537_) == 0)
{
lean_object* v_a_2550_; lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
v_a_2551_ = lean_ctor_get(v___x_2549_, 1);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2549_, 2);
v___x_2552_ = lean_box(0);
v___y_2494_ = v___x_2540_;
v___y_2495_ = v___y_2538_;
v___y_2496_ = v_a_2551_;
v___y_2497_ = v___x_2544_;
v___y_2498_ = v_val_2548_;
v___y_2499_ = v_a_2550_;
v___y_2500_ = v___x_2552_;
goto v___jp_2493_;
}
else
{
lean_object* v_a_2553_; lean_object* v_a_2554_; lean_object* v_val_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_a_2553_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2553_);
v_a_2554_ = lean_ctor_get(v___x_2549_, 1);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2549_, 2);
v_val_2555_ = lean_ctor_get(v_tac_x3f_2537_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_tac_x3f_2537_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v_tac_x3f_2537_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_val_2555_);
lean_dec(v_tac_x3f_2537_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_val_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
v___y_2494_ = v___x_2540_;
v___y_2495_ = v___y_2538_;
v___y_2496_ = v_a_2554_;
v___y_2497_ = v___x_2544_;
v___y_2498_ = v_val_2548_;
v___y_2499_ = v_a_2553_;
v___y_2500_ = v___x_2560_;
goto v___jp_2493_;
}
}
}
}
else
{
lean_dec(v_val_2548_);
lean_dec(v_tac_x3f_2537_);
return v___x_2549_;
}
}
}
}
v___jp_2493_:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_Fmt_fmt_x3f(v___y_2500_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v_a_2503_; size_t v_sz_2504_; lean_object* v___x_2505_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
v_a_2503_ = lean_ctor_get(v___x_2501_, 1);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2501_, 2);
v_sz_2504_ = lean_array_size(v___y_2498_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCAlts_spec__1(v_sz_2504_, v___y_2497_, v___y_2498_, v___y_2495_, v_a_2503_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2522_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_a_2507_ = lean_ctor_get(v___x_2505_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2509_ = v___x_2505_;
v_isShared_2510_ = v_isSharedCheck_2522_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2522_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2511_ = lean_mk_empty_array_with_capacity(v___y_2494_);
v___x_2512_ = lean_array_push(v___x_2511_, v___y_2499_);
v___x_2513_ = lean_array_push(v___x_2512_, v_a_2502_);
v___x_2514_ = 0;
v___x_2515_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2515_, 0, v___x_2492_);
lean_ctor_set_uint8(v___x_2515_, 1, v___x_2514_);
lean_ctor_set_uint8(v___x_2515_, 2, v___x_2514_);
lean_ctor_set_uint8(v___x_2515_, 3, v___x_2514_);
v___x_2516_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2513_, v___x_2515_);
v___x_2517_ = 0;
v___x_2518_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v___x_2516_, v_a_2506_, v___x_2517_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2518_);
v___x_2520_ = v___x_2509_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_a_2507_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_a_2502_);
lean_dec_ref(v___y_2499_);
v_a_2523_ = lean_ctor_get(v___x_2505_, 0);
v_a_2524_ = lean_ctor_get(v___x_2505_, 1);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2505_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_inc(v_a_2523_);
lean_dec(v___x_2505_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2523_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_dec_ref(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v___x_2501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCAlts___boxed(lean_object* v_x_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Fmt_fmtVCAlts(v_x_2572_, v_a_2573_, v_a_2574_);
lean_dec_ref(v_a_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1(){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2582_ = l_Lean_Fmt_fmtAttribute;
v___x_2583_ = ((lean_object*)(l_Lean_Fmt_fmtVCAlts___closed__1));
v___x_2584_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___closed__1));
v___x_2585_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtVCAlts___boxed), 3, 0);
v___x_2586_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2582_, v___x_2583_, v___x_2584_, v___x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1___boxed(lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1();
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMVCGen(lean_object* v_x_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = ((lean_object*)(l_Lean_Fmt_fmtMVCGen___closed__1));
lean_inc(v_x_2607_);
v___x_2611_ = l_Lean_Syntax_isOfKind(v_x_2607_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_dec(v_x_2607_);
v___x_2612_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v_a_2609_);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; lean_object* v_cfg_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; 
v___x_2614_ = lean_unsigned_to_nat(1u);
v_cfg_2615_ = l_Lean_Syntax_getArg(v_x_2607_, v___x_2614_);
v___x_2616_ = ((lean_object*)(l_Lean_Fmt_fmtMVCGen___closed__3));
lean_inc(v_cfg_2615_);
v___x_2617_ = l_Lean_Syntax_isOfKind(v_cfg_2615_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v_cfg_2615_);
lean_dec(v_x_2607_);
v___x_2691_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
lean_ctor_set(v___x_2692_, 1, v_a_2609_);
return v___x_2692_;
}
else
{
lean_object* v___x_2693_; lean_object* v_mvcgenTk_2694_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v_vcAlts_x3f_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v_invariantAlts_x3f_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v_lbTk_x3f_2738_; lean_object* v_args_x3f_2739_; lean_object* v_rbTk_x3f_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2693_ = lean_unsigned_to_nat(0u);
v_mvcgenTk_2694_ = l_Lean_Syntax_getArg(v_x_2607_, v___x_2693_);
v___x_2756_ = lean_unsigned_to_nat(2u);
v___x_2757_ = l_Lean_Syntax_getArg(v_x_2607_, v___x_2756_);
v___x_2758_ = l_Lean_Syntax_isNone(v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2757_);
v___x_2760_ = l_Lean_Syntax_matchesNull(v___x_2757_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec(v___x_2757_);
lean_dec(v_mvcgenTk_2694_);
lean_dec(v_cfg_2615_);
lean_dec(v_x_2607_);
v___x_2761_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v_a_2609_);
return v___x_2762_;
}
else
{
lean_object* v_lbTk_x3f_2763_; lean_object* v___x_2764_; lean_object* v_rbTk_x3f_2765_; lean_object* v_args_x3f_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_lbTk_x3f_2763_ = l_Lean_Syntax_getArg(v___x_2757_, v___x_2693_);
v___x_2764_ = l_Lean_Syntax_getArg(v___x_2757_, v___x_2614_);
v_rbTk_x3f_2765_ = l_Lean_Syntax_getArg(v___x_2757_, v___x_2756_);
lean_dec(v___x_2757_);
v_args_x3f_2766_ = l_Lean_Syntax_getArgs(v___x_2764_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_lbTk_x3f_2763_);
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v_args_x3f_2766_);
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_rbTk_x3f_2765_);
v_lbTk_x3f_2738_ = v___x_2767_;
v_args_x3f_2739_ = v___x_2768_;
v_rbTk_x3f_2740_ = v___x_2769_;
v___y_2741_ = v_a_2608_;
v___y_2742_ = v_a_2609_;
goto v___jp_2737_;
}
}
else
{
lean_object* v___x_2770_; 
lean_dec(v___x_2757_);
v___x_2770_ = lean_box(0);
v_lbTk_x3f_2738_ = v___x_2770_;
v_args_x3f_2739_ = v___x_2770_;
v_rbTk_x3f_2740_ = v___x_2770_;
v___y_2741_ = v_a_2608_;
v___y_2742_ = v_a_2609_;
goto v___jp_2737_;
}
v___jp_2695_:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_Fmt_fmtVCGenHead(v_mvcgenTk_2694_, v_cfg_2615_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2703_) == 0)
{
if (lean_obj_tag(v___y_2698_) == 0)
{
lean_object* v_a_2704_; lean_object* v_a_2705_; lean_object* v___x_2706_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
v_a_2705_ = lean_ctor_get(v___x_2703_, 1);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2703_, 2);
v___x_2706_ = lean_box(0);
v___y_2669_ = v___y_2696_;
v___y_2670_ = v___y_2697_;
v___y_2671_ = v_a_2704_;
v___y_2672_ = v_a_2705_;
v___y_2673_ = v___y_2701_;
v___y_2674_ = v_vcAlts_x3f_2700_;
v___y_2675_ = v___y_2699_;
v___y_2676_ = v___x_2706_;
goto v___jp_2668_;
}
else
{
lean_object* v_a_2707_; lean_object* v_a_2708_; lean_object* v_val_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
v_a_2707_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2707_);
v_a_2708_ = lean_ctor_get(v___x_2703_, 1);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2703_, 2);
v_val_2709_ = lean_ctor_get(v___y_2698_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___y_2698_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___y_2698_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_val_2709_);
lean_dec(v___y_2698_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_val_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
v___y_2669_ = v___y_2696_;
v___y_2670_ = v___y_2697_;
v___y_2671_ = v_a_2707_;
v___y_2672_ = v_a_2708_;
v___y_2673_ = v___y_2701_;
v___y_2674_ = v_vcAlts_x3f_2700_;
v___y_2675_ = v___y_2699_;
v___y_2676_ = v___x_2714_;
goto v___jp_2668_;
}
}
}
}
else
{
lean_dec(v_vcAlts_x3f_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
return v___x_2703_;
}
}
v___jp_2717_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2724_ = lean_unsigned_to_nat(4u);
v___x_2725_ = l_Lean_Syntax_getArg(v_x_2607_, v___x_2724_);
lean_dec(v_x_2607_);
v___x_2726_ = l_Lean_Syntax_isNone(v___x_2725_);
if (v___x_2726_ == 0)
{
uint8_t v___x_2727_; 
lean_inc(v___x_2725_);
v___x_2727_ = l_Lean_Syntax_matchesNull(v___x_2725_, v___x_2614_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec(v___x_2725_);
lean_dec(v_invariantAlts_x3f_2721_);
lean_dec(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec(v_mvcgenTk_2694_);
lean_dec(v_cfg_2615_);
v___x_2728_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v___y_2723_);
return v___x_2729_;
}
else
{
lean_object* v_vcAlts_x3f_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_vcAlts_x3f_2730_ = l_Lean_Syntax_getArg(v___x_2725_, v___x_2693_);
lean_dec(v___x_2725_);
v___x_2731_ = ((lean_object*)(l_Lean_Fmt_fmtVCAlts___closed__1));
lean_inc(v_vcAlts_x3f_2730_);
v___x_2732_ = l_Lean_Syntax_isOfKind(v_vcAlts_x3f_2730_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_dec(v_vcAlts_x3f_2730_);
lean_dec(v_invariantAlts_x3f_2721_);
lean_dec(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec(v_mvcgenTk_2694_);
lean_dec(v_cfg_2615_);
v___x_2733_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
lean_ctor_set(v___x_2734_, 1, v___y_2723_);
return v___x_2734_;
}
else
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2735_, 0, v_vcAlts_x3f_2730_);
v___y_2696_ = v___y_2718_;
v___y_2697_ = v_invariantAlts_x3f_2721_;
v___y_2698_ = v___y_2719_;
v___y_2699_ = v___y_2720_;
v_vcAlts_x3f_2700_ = v___x_2735_;
v___y_2701_ = v___y_2722_;
v___y_2702_ = v___y_2723_;
goto v___jp_2695_;
}
}
}
else
{
lean_object* v___x_2736_; 
lean_dec(v___x_2725_);
v___x_2736_ = lean_box(0);
v___y_2696_ = v___y_2718_;
v___y_2697_ = v_invariantAlts_x3f_2721_;
v___y_2698_ = v___y_2719_;
v___y_2699_ = v___y_2720_;
v_vcAlts_x3f_2700_ = v___x_2736_;
v___y_2701_ = v___y_2722_;
v___y_2702_ = v___y_2723_;
goto v___jp_2695_;
}
}
v___jp_2737_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v___x_2743_ = lean_unsigned_to_nat(3u);
v___x_2744_ = l_Lean_Syntax_getArg(v_x_2607_, v___x_2743_);
v___x_2745_ = l_Lean_Syntax_isNone(v___x_2744_);
if (v___x_2745_ == 0)
{
uint8_t v___x_2746_; 
lean_inc(v___x_2744_);
v___x_2746_ = l_Lean_Syntax_matchesNull(v___x_2744_, v___x_2614_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec(v___x_2744_);
lean_dec(v_rbTk_x3f_2740_);
lean_dec(v_args_x3f_2739_);
lean_dec(v_lbTk_x3f_2738_);
lean_dec(v_mvcgenTk_2694_);
lean_dec(v_cfg_2615_);
lean_dec(v_x_2607_);
v___x_2747_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
lean_ctor_set(v___x_2748_, 1, v___y_2742_);
return v___x_2748_;
}
else
{
lean_object* v_invariantAlts_x3f_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_invariantAlts_x3f_2749_ = l_Lean_Syntax_getArg(v___x_2744_, v___x_2693_);
lean_dec(v___x_2744_);
v___x_2750_ = ((lean_object*)(l_Lean_Fmt_fmtMVCGen___closed__5));
lean_inc(v_invariantAlts_x3f_2749_);
v___x_2751_ = l_Lean_Syntax_isOfKind(v_invariantAlts_x3f_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_dec(v_invariantAlts_x3f_2749_);
lean_dec(v_rbTk_x3f_2740_);
lean_dec(v_args_x3f_2739_);
lean_dec(v_lbTk_x3f_2738_);
lean_dec(v_mvcgenTk_2694_);
lean_dec(v_cfg_2615_);
lean_dec(v_x_2607_);
v___x_2752_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
lean_ctor_set(v___x_2753_, 1, v___y_2742_);
return v___x_2753_;
}
else
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_invariantAlts_x3f_2749_);
v___y_2718_ = v_rbTk_x3f_2740_;
v___y_2719_ = v_args_x3f_2739_;
v___y_2720_ = v_lbTk_x3f_2738_;
v_invariantAlts_x3f_2721_ = v___x_2754_;
v___y_2722_ = v___y_2741_;
v___y_2723_ = v___y_2742_;
goto v___jp_2717_;
}
}
}
else
{
lean_object* v___x_2755_; 
lean_dec(v___x_2744_);
v___x_2755_ = lean_box(0);
v___y_2718_ = v_rbTk_x3f_2740_;
v___y_2719_ = v_args_x3f_2739_;
v___y_2720_ = v_lbTk_x3f_2738_;
v_invariantAlts_x3f_2721_ = v___x_2755_;
v___y_2722_ = v___y_2741_;
v___y_2723_ = v___y_2742_;
goto v___jp_2717_;
}
}
}
v___jp_2618_:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Fmt_fmt_x3f(v___y_2624_, v___y_2621_, v___y_2619_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2646_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_a_2627_ = lean_ctor_get(v___x_2625_, 1);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2629_ = v___x_2625_;
v_isShared_2630_ = v_isSharedCheck_2646_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2646_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2631_ = 0;
v___x_2632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2632_, 0, v___y_2623_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*1, v___x_2631_);
v___x_2633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2633_, 0, v_a_2626_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*1, v___x_2631_);
v___x_2634_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2634_, 0, v___y_2620_);
lean_ctor_set_uint8(v___x_2634_, sizeof(void*)*1, v___x_2617_);
v___x_2635_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2635_, 0, v___y_2622_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*1, v___x_2617_);
v___x_2636_ = lean_unsigned_to_nat(4u);
v___x_2637_ = lean_mk_empty_array_with_capacity(v___x_2636_);
v___x_2638_ = lean_array_push(v___x_2637_, v___x_2634_);
v___x_2639_ = lean_array_push(v___x_2638_, v___x_2635_);
v___x_2640_ = lean_array_push(v___x_2639_, v___x_2632_);
v___x_2641_ = lean_array_push(v___x_2640_, v___x_2633_);
v___x_2642_ = l_Lean_Fmt_Layouts_blocks(v___x_2641_, v___x_2617_);
lean_dec_ref(v___x_2641_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2642_);
v___x_2644_ = v___x_2629_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_a_2627_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
else
{
lean_dec_ref(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2620_);
return v___x_2625_;
}
}
v___jp_2647_:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Fmt_fmt_x3f(v___y_2653_, v___y_2650_, v___y_2649_);
if (lean_obj_tag(v___x_2654_) == 0)
{
if (lean_obj_tag(v___y_2652_) == 0)
{
lean_object* v_a_2655_; lean_object* v_a_2656_; lean_object* v___x_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
v_a_2656_ = lean_ctor_get(v___x_2654_, 1);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2654_, 2);
v___x_2657_ = lean_box(0);
v___y_2619_ = v_a_2656_;
v___y_2620_ = v___y_2648_;
v___y_2621_ = v___y_2650_;
v___y_2622_ = v___y_2651_;
v___y_2623_ = v_a_2655_;
v___y_2624_ = v___x_2657_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2658_; lean_object* v_a_2659_; lean_object* v_val_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v_a_2658_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2658_);
v_a_2659_ = lean_ctor_get(v___x_2654_, 1);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2654_, 2);
v_val_2660_ = lean_ctor_get(v___y_2652_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___y_2652_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___y_2652_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_val_2660_);
lean_dec(v___y_2652_);
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
v___y_2619_ = v_a_2659_;
v___y_2620_ = v___y_2648_;
v___y_2621_ = v___y_2650_;
v___y_2622_ = v___y_2651_;
v___y_2623_ = v_a_2658_;
v___y_2624_ = v___x_2665_;
goto v___jp_2618_;
}
}
}
}
else
{
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec_ref(v___y_2648_);
return v___x_2654_;
}
}
v___jp_2668_:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_Fmt_fmtVCGenSimpArgs(v___y_2675_, v___y_2676_, v___y_2669_, v___y_2673_, v___y_2672_);
if (lean_obj_tag(v___x_2677_) == 0)
{
if (lean_obj_tag(v___y_2670_) == 0)
{
lean_object* v_a_2678_; lean_object* v_a_2679_; lean_object* v___x_2680_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
v_a_2679_ = lean_ctor_get(v___x_2677_, 1);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2677_, 2);
v___x_2680_ = lean_box(0);
v___y_2648_ = v___y_2671_;
v___y_2649_ = v_a_2679_;
v___y_2650_ = v___y_2673_;
v___y_2651_ = v_a_2678_;
v___y_2652_ = v___y_2674_;
v___y_2653_ = v___x_2680_;
goto v___jp_2647_;
}
else
{
lean_object* v_a_2681_; lean_object* v_a_2682_; lean_object* v_val_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
v_a_2681_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2681_);
v_a_2682_ = lean_ctor_get(v___x_2677_, 1);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2677_, 2);
v_val_2683_ = lean_ctor_get(v___y_2670_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___y_2670_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___y_2670_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_val_2683_);
lean_dec(v___y_2670_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_val_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
v___y_2648_ = v___y_2671_;
v___y_2649_ = v_a_2682_;
v___y_2650_ = v___y_2673_;
v___y_2651_ = v_a_2681_;
v___y_2652_ = v___y_2674_;
v___y_2653_ = v___x_2688_;
goto v___jp_2647_;
}
}
}
}
else
{
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
return v___x_2677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMVCGen___boxed(lean_object* v_x_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_Fmt_fmtMVCGen(v_x_2771_, v_a_2772_, v_a_2773_);
lean_dec_ref(v_a_2772_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1(){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2781_ = l_Lean_Fmt_fmtAttribute;
v___x_2782_ = ((lean_object*)(l_Lean_Fmt_fmtMVCGen___closed__1));
v___x_2783_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___closed__1));
v___x_2784_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMVCGen___boxed), 3, 0);
v___x_2785_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2781_, v___x_2782_, v___x_2783_, v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1___boxed(lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1();
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMVCGenHint(lean_object* v_x_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = ((lean_object*)(l_Lean_Fmt_fmtMVCGenHint___closed__1));
lean_inc(v_x_2794_);
v___x_2798_ = l_Lean_Syntax_isOfKind(v_x_2794_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec(v_x_2794_);
v___x_2799_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v_a_2796_);
return v___x_2800_;
}
else
{
lean_object* v___x_2801_; lean_object* v_cfg_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; 
v___x_2801_ = lean_unsigned_to_nat(1u);
v_cfg_2802_ = l_Lean_Syntax_getArg(v_x_2794_, v___x_2801_);
v___x_2803_ = ((lean_object*)(l_Lean_Fmt_fmtMVCGen___closed__3));
lean_inc(v_cfg_2802_);
v___x_2804_ = l_Lean_Syntax_isOfKind(v_cfg_2802_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v_cfg_2802_);
lean_dec(v_x_2794_);
v___x_2829_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v_a_2796_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v_mvcgenTk_2832_; lean_object* v_lbTk_x3f_2834_; lean_object* v_args_x3f_2835_; lean_object* v_rbTk_x3f_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v___x_2831_ = lean_unsigned_to_nat(0u);
v_mvcgenTk_2832_ = l_Lean_Syntax_getArg(v_x_2794_, v___x_2831_);
v___x_2853_ = lean_unsigned_to_nat(2u);
v___x_2854_ = l_Lean_Syntax_getArg(v_x_2794_, v___x_2853_);
lean_dec(v_x_2794_);
v___x_2855_ = l_Lean_Syntax_isNone(v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2856_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2854_);
v___x_2857_ = l_Lean_Syntax_matchesNull(v___x_2854_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec(v___x_2854_);
lean_dec(v_mvcgenTk_2832_);
lean_dec(v_cfg_2802_);
v___x_2858_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v_a_2796_);
return v___x_2859_;
}
else
{
lean_object* v_lbTk_x3f_2860_; lean_object* v___x_2861_; lean_object* v_rbTk_x3f_2862_; lean_object* v_args_x3f_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_lbTk_x3f_2860_ = l_Lean_Syntax_getArg(v___x_2854_, v___x_2831_);
v___x_2861_ = l_Lean_Syntax_getArg(v___x_2854_, v___x_2801_);
v_rbTk_x3f_2862_ = l_Lean_Syntax_getArg(v___x_2854_, v___x_2853_);
lean_dec(v___x_2854_);
v_args_x3f_2863_ = l_Lean_Syntax_getArgs(v___x_2861_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_lbTk_x3f_2860_);
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v_args_x3f_2863_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_rbTk_x3f_2862_);
v_lbTk_x3f_2834_ = v___x_2864_;
v_args_x3f_2835_ = v___x_2865_;
v_rbTk_x3f_2836_ = v___x_2866_;
v___y_2837_ = v_a_2795_;
v___y_2838_ = v_a_2796_;
goto v___jp_2833_;
}
}
else
{
lean_object* v___x_2867_; 
lean_dec(v___x_2854_);
v___x_2867_ = lean_box(0);
v_lbTk_x3f_2834_ = v___x_2867_;
v_args_x3f_2835_ = v___x_2867_;
v_rbTk_x3f_2836_ = v___x_2867_;
v___y_2837_ = v_a_2795_;
v___y_2838_ = v_a_2796_;
goto v___jp_2833_;
}
v___jp_2833_:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Fmt_fmtVCGenHead(v_mvcgenTk_2832_, v_cfg_2802_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
if (lean_obj_tag(v_args_x3f_2835_) == 0)
{
lean_object* v_a_2840_; lean_object* v_a_2841_; lean_object* v___x_2842_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
v_a_2841_ = lean_ctor_get(v___x_2839_, 1);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2839_, 2);
v___x_2842_ = lean_box(0);
v___y_2806_ = v_a_2840_;
v___y_2807_ = v___y_2837_;
v___y_2808_ = v_lbTk_x3f_2834_;
v___y_2809_ = v_a_2841_;
v___y_2810_ = v_rbTk_x3f_2836_;
v___y_2811_ = v___x_2842_;
goto v___jp_2805_;
}
else
{
lean_object* v_a_2843_; lean_object* v_a_2844_; lean_object* v_val_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2843_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2843_);
v_a_2844_ = lean_ctor_get(v___x_2839_, 1);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2839_, 2);
v_val_2845_ = lean_ctor_get(v_args_x3f_2835_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_args_x3f_2835_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v_args_x3f_2835_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_val_2845_);
lean_dec(v_args_x3f_2835_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_val_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
v___y_2806_ = v_a_2843_;
v___y_2807_ = v___y_2837_;
v___y_2808_ = v_lbTk_x3f_2834_;
v___y_2809_ = v_a_2844_;
v___y_2810_ = v_rbTk_x3f_2836_;
v___y_2811_ = v___x_2850_;
goto v___jp_2805_;
}
}
}
}
else
{
lean_dec(v_rbTk_x3f_2836_);
lean_dec(v_args_x3f_2835_);
lean_dec(v_lbTk_x3f_2834_);
return v___x_2839_;
}
}
}
v___jp_2805_:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Fmt_fmtVCGenSimpArgs(v___y_2808_, v___y_2811_, v___y_2810_, v___y_2807_, v___y_2809_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2828_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_a_2814_ = lean_ctor_get(v___x_2812_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2816_ = v___x_2812_;
v_isShared_2817_ = v_isSharedCheck_2828_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2828_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2818_ = lean_unsigned_to_nat(2u);
v___x_2819_ = lean_mk_empty_array_with_capacity(v___x_2818_);
v___x_2820_ = lean_array_push(v___x_2819_, v___y_2806_);
v___x_2821_ = lean_array_push(v___x_2820_, v_a_2813_);
v___x_2822_ = 0;
v___x_2823_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2823_, 0, v___x_2804_);
lean_ctor_set_uint8(v___x_2823_, 1, v___x_2822_);
lean_ctor_set_uint8(v___x_2823_, 2, v___x_2822_);
lean_ctor_set_uint8(v___x_2823_, 3, v___x_2822_);
v___x_2824_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2821_, v___x_2823_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v___x_2824_);
v___x_2826_ = v___x_2816_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_a_2814_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
else
{
lean_dec_ref(v___y_2806_);
return v___x_2812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMVCGenHint___boxed(lean_object* v_x_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Fmt_fmtMVCGenHint(v_x_2868_, v_a_2869_, v_a_2870_);
lean_dec_ref(v_a_2869_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1(){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2878_ = l_Lean_Fmt_fmtAttribute;
v___x_2879_ = ((lean_object*)(l_Lean_Fmt_fmtMVCGenHint___closed__1));
v___x_2880_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___closed__1));
v___x_2881_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMVCGenHint___boxed), 3, 0);
v___x_2882_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2878_, v___x_2879_, v___x_2880_, v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1___boxed(lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1();
return v_res_2884_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_WP_Tactic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax(uint8_t builtin) {
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
res = runtime_initialize_Lean_Fmt_Formatters_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMClear___regBuiltin_Lean_Fmt_fmtMClear__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExact___regBuiltin_Lean_Fmt_fmtMExact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMPure___regBuiltin_Lean_Fmt_fmtMPure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRenameI___regBuiltin_Lean_Fmt_fmtMRenameI__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecialize___regBuiltin_Lean_Fmt_fmtMSpecialize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecializePure___regBuiltin_Lean_Fmt_fmtMSpecializePure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefine___regBuiltin_Lean_Fmt_fmtMRefine__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntro___regBuiltin_Lean_Fmt_fmtMIntro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevert___regBuiltin_Lean_Fmt_fmtMRevert__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoBind___regBuiltin_Lean_Fmt_fmtMSpecNoBind__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpecNoSimp___regBuiltin_Lean_Fmt_fmtMSpecNoSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMSpec___regBuiltin_Lean_Fmt_fmtMSpec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMExists___regBuiltin_Lean_Fmt_fmtMExists__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMDup___regBuiltin_Lean_Fmt_fmtMDup__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMHave___regBuiltin_Lean_Fmt_fmtMHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMReplace___regBuiltin_Lean_Fmt_fmtMReplace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatAlts___regBuiltin_Lean_Fmt_fmtMCasesPatAlts__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatOne___regBuiltin_Lean_Fmt_fmtMCasesPatOne__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatClear___regBuiltin_Lean_Fmt_fmtMCasesPatClear__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatTuple___regBuiltin_Lean_Fmt_fmtMCasesPatTuple__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatParen___regBuiltin_Lean_Fmt_fmtMCasesPatParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPure___regBuiltin_Lean_Fmt_fmtMCasesPatPure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStateful___regBuiltin_Lean_Fmt_fmtMCasesPatStateful__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatPureAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatPureAbbrev__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCasesPatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMCasesPatStatefulAbbrev__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMCases___regBuiltin_Lean_Fmt_fmtMCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatOne___regBuiltin_Lean_Fmt_fmtMRefinePatOne__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatTuple___regBuiltin_Lean_Fmt_fmtMRefinePatTuple__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatParen___regBuiltin_Lean_Fmt_fmtMRefinePatParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPure___regBuiltin_Lean_Fmt_fmtMRefinePatPure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStateful___regBuiltin_Lean_Fmt_fmtMRefinePatStateful__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatHole___regBuiltin_Lean_Fmt_fmtMRefinePatHole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatPureAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatPureAbbrev__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRefinePatStatefulAbbrev___regBuiltin_Lean_Fmt_fmtMRefinePatStatefulAbbrev__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatCases___regBuiltin_Lean_Fmt_fmtMIntroPatCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMIntroPatForall___regBuiltin_Lean_Fmt_fmtMIntroPatForall__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatOne___regBuiltin_Lean_Fmt_fmtMRevertPatOne__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMRevertPatForall___regBuiltin_Lean_Fmt_fmtMRevertPatForall__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtVCAlts___regBuiltin_Lean_Fmt_fmtVCAlts__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGen___regBuiltin_Lean_Fmt_fmtMVCGen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax_0__Lean_Fmt_fmtMVCGenHint___regBuiltin_Lean_Fmt_fmtMVCGenHint__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Std_WP_Tactic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Tactic_Do_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
