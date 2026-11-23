// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.WP.Tactic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.WP.Tactic import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_tacticOptConfigItems___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_Layouts_alt(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object*);
lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
static const lean_string_object l_Lean_Fmt_fmtSpecAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtSpecAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSpecAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtSpecAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSpecAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Fmt_fmtSpecAttr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtSpecAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l_Lean_Fmt_fmtSpecAttr___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtSpecAttr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSpecAttr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSpecAttr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtSpecAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 37, 203, 230, 106, 254, 64, 102)}};
static const lean_object* l_Lean_Fmt_fmtSpecAttr___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSpecAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSpecAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtSpecAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 191, 64, 219, 28, 55, 8, 150)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtInvariantAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtInvariantAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtInvariantAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__3_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtInvariantAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__5_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtInvariantAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_Lean_Fmt_fmtInvariantAlt___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInvariantAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInvariantAlt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtInvariantAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invariantAlts"};
static const lean_object* l_Lean_Fmt_fmtInvariantAlts___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 41, 254, 250, 50, 69, 99, 10)}};
static const lean_object* l_Lean_Fmt_fmtInvariantAlts___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtInvariantAlts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invariantsKW"};
static const lean_object* l_Lean_Fmt_fmtInvariantAlts___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlts___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlts___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlts___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtInvariantAlts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 87, 251, 76, 123, 116, 93, 232)}};
static const lean_object* l_Lean_Fmt_fmtInvariantAlts___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtInvariantAlts___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInvariantAlts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInvariantAlts___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtInvariantAlts"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 153, 119, 153, 254, 230, 4, 154)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtFrameAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "frameAlt"};
static const lean_object* l_Lean_Fmt_fmtFrameAlt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtFrameAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtFrameAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtFrameAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtFrameAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 154, 201, 239, 176, 247, 171, 168)}};
static const lean_object* l_Lean_Fmt_fmtFrameAlt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtFrameAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtFrameAlt___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtFrameAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtFrameAlt___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtFrameAlt___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFrameAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFrameAlt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenHead_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenHead_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtVCGenHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtVCGenHead___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtVCGenHead___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenHead(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenHead___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtVCGenSimpArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtVCGenSimpArgs___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtVCGenSimpArgs___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtVCGenSimpArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtVCGenSimpArgs___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtVCGenSimpArgs___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtVCGenSimpArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtVCGenSimpArgs___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtVCGenSimpArgs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenSimpArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenSimpArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtVCGenDischargeGrind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "vcgenDischargeGrind"};
static const lean_object* l_Lean_Fmt_fmtVCGenDischargeGrind___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtVCGenDischargeGrind___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtVCGenDischargeGrind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 199, 17, 154, 227, 108, 8, 170)}};
static const lean_object* l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenDischargeGrind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenDischargeGrind___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtVCGenDischargeGrind"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 30, 75, 37, 37, 242, 21, 125)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtVCGenDischargeTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "vcgenDischargeTactic"};
static const lean_object* l_Lean_Fmt_fmtVCGenDischargeTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtVCGenDischargeTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtVCGenDischargeTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 78, 68, 156, 106, 197, 226, 93)}};
static const lean_object* l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenDischargeTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenDischargeTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtVCGenDischargeTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 116, 54, 75, 102, 168, 77, 133)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenLike_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenLike_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenLike___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGen_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGen_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtVCGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l_Lean_Fmt_fmtVCGen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtVCGen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtVCGen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 196, 10, 243, 239, 189, 222, 13)}};
static const lean_object* l_Lean_Fmt_fmtVCGen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtVCGen___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtVCGen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Fmt_fmtVCGen___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtVCGen___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtVCGen___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGen___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGen___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtVCGen___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Fmt_fmtVCGen___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtVCGen___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtVCGen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 56, 122, 198, 123, 248, 163, 78)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindVCGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Fmt_fmtGrindVCGen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindVCGen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindVCGen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindVCGen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindVCGen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindVCGen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindVCGen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtInvariantAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindVCGen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindVCGen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindVCGen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindVCGen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindVCGen___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtVCGen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 229, 87, 15, 155, 212, 124, 96)}};
static const lean_object* l_Lean_Fmt_fmtGrindVCGen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindVCGen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindVCGen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindVCGen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindVCGen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSpecAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 181, 45, 109, 118, 26, 90, 188)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSpecAttr(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___y_16_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtSpecAttr___closed__4));
lean_inc(v_x_10_);
v___x_14_ = l_Lean_Syntax_isOfKind(v_x_10_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_dec(v_x_10_);
v___x_37_ = l_Lean_Fmt_Error_partialFormatter;
v___x_38_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v_a_12_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; lean_object* v_specTk_40_; lean_object* v_prio_x3f_42_; lean_object* v___y_43_; lean_object* v___y_44_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_39_ = lean_unsigned_to_nat(0u);
v_specTk_40_ = l_Lean_Syntax_getArg(v_x_10_, v___x_39_);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = l_Lean_Syntax_getArg(v_x_10_, v___x_59_);
lean_dec(v_x_10_);
v___x_61_ = l_Lean_Syntax_isNone(v___x_60_);
if (v___x_61_ == 0)
{
uint8_t v___x_62_; 
lean_inc(v___x_60_);
v___x_62_ = l_Lean_Syntax_matchesNull(v___x_60_, v___x_59_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v___x_60_);
lean_dec(v_specTk_40_);
v___x_63_ = l_Lean_Fmt_Error_partialFormatter;
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v_a_12_);
return v___x_64_;
}
else
{
lean_object* v_prio_x3f_65_; lean_object* v___x_66_; 
v_prio_x3f_65_ = l_Lean_Syntax_getArg(v___x_60_, v___x_39_);
lean_dec(v___x_60_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v_prio_x3f_65_);
v_prio_x3f_42_ = v___x_66_;
v___y_43_ = v_a_11_;
v___y_44_ = v_a_12_;
goto v___jp_41_;
}
}
else
{
lean_object* v___x_67_; 
lean_dec(v___x_60_);
v___x_67_ = lean_box(0);
v_prio_x3f_42_ = v___x_67_;
v___y_43_ = v_a_11_;
v___y_44_ = v_a_12_;
goto v___jp_41_;
}
v___jp_41_:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Fmt_fmt(v_specTk_40_, v___y_43_, v___y_44_);
if (lean_obj_tag(v___x_45_) == 0)
{
if (lean_obj_tag(v_prio_x3f_42_) == 0)
{
lean_object* v_a_46_; lean_object* v_a_47_; lean_object* v___x_48_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_a_46_);
v_a_47_ = lean_ctor_get(v___x_45_, 1);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_45_, 2);
v___x_48_ = lean_box(0);
v___y_16_ = v___y_43_;
v___y_17_ = v_a_46_;
v___y_18_ = v_a_47_;
v___y_19_ = v___x_48_;
goto v___jp_15_;
}
else
{
lean_object* v_a_49_; lean_object* v_a_50_; lean_object* v_val_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_a_49_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_a_49_);
v_a_50_ = lean_ctor_get(v___x_45_, 1);
lean_inc(v_a_50_);
lean_dec_ref_known(v___x_45_, 2);
v_val_51_ = lean_ctor_get(v_prio_x3f_42_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v_prio_x3f_42_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v_prio_x3f_42_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_val_51_);
lean_dec(v_prio_x3f_42_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_val_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
v___y_16_ = v___y_43_;
v___y_17_ = v_a_49_;
v___y_18_ = v_a_50_;
v___y_19_ = v___x_56_;
goto v___jp_15_;
}
}
}
}
else
{
lean_dec(v_prio_x3f_42_);
return v___x_45_;
}
}
}
v___jp_15_:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Fmt_fmt_x3f(v___y_19_, v___y_16_, v___y_18_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_36_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_a_22_ = lean_ctor_get(v___x_20_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_36_ == 0)
{
v___x_24_ = v___x_20_;
v_isShared_25_ = v_isSharedCheck_36_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_36_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_26_ = lean_unsigned_to_nat(2u);
v___x_27_ = lean_mk_empty_array_with_capacity(v___x_26_);
v___x_28_ = lean_array_push(v___x_27_, v___y_17_);
v___x_29_ = lean_array_push(v___x_28_, v_a_21_);
v___x_30_ = 0;
v___x_31_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_31_, 0, v___x_14_);
lean_ctor_set_uint8(v___x_31_, 1, v___x_30_);
lean_ctor_set_uint8(v___x_31_, 2, v___x_30_);
lean_ctor_set_uint8(v___x_31_, 3, v___x_30_);
v___x_32_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_29_, v___x_31_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_32_);
v___x_34_ = v___x_24_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_a_22_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
else
{
lean_dec_ref(v___y_17_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSpecAttr___boxed(lean_object* v_x_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Fmt_fmtSpecAttr(v_x_68_, v_a_69_, v_a_70_);
lean_dec_ref(v_a_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1(){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = l_Lean_Fmt_fmtAttribute;
v___x_80_ = ((lean_object*)(l_Lean_Fmt_fmtSpecAttr___closed__4));
v___x_81_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___closed__2));
v___x_82_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSpecAttr___boxed), 3, 0);
v___x_83_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_79_, v___x_80_, v___x_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1___boxed(lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInvariantAlt(lean_object* v_x_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlt___closed__2));
lean_inc(v_x_109_);
v___x_113_ = l_Lean_Syntax_isOfKind(v_x_109_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlt___closed__4));
lean_inc(v_x_109_);
v___x_115_ = l_Lean_Syntax_isOfKind(v_x_109_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v_x_109_);
v___x_116_ = l_Lean_Fmt_Error_partialFormatter;
v___x_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_a_111_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_109_, v___x_118_);
v___x_120_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlt___closed__6));
lean_inc(v___x_119_);
v___x_121_ = l_Lean_Syntax_isOfKind(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v___x_119_);
lean_dec(v_x_109_);
v___x_122_ = l_Lean_Fmt_Error_partialFormatter;
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_a_111_);
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v_pipeTk_125_; lean_object* v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v_pipeTk_125_ = l_Lean_Syntax_getArg(v_x_109_, v___x_124_);
v___x_126_ = l_Lean_Fmt_fmt(v_pipeTk_125_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v_a_128_; lean_object* v___x_129_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
v_a_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_126_, 2);
v___x_129_ = l_Lean_Fmt_fmt(v___x_119_, v_a_110_, v_a_128_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v_a_131_; lean_object* v___x_132_; lean_object* v_arrowTk_133_; lean_object* v___x_134_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
v_a_131_ = lean_ctor_get(v___x_129_, 1);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_129_, 2);
v___x_132_ = lean_unsigned_to_nat(2u);
v_arrowTk_133_ = l_Lean_Syntax_getArg(v_x_109_, v___x_132_);
v___x_134_ = l_Lean_Fmt_fmt(v_arrowTk_133_, v_a_110_, v_a_131_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
v_a_136_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_134_, 2);
v___x_137_ = lean_unsigned_to_nat(3u);
v___x_138_ = l_Lean_Syntax_getArg(v_x_109_, v___x_137_);
lean_dec(v_x_109_);
v___x_139_ = l_Lean_Fmt_fmt(v___x_138_, v_a_110_, v_a_136_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_156_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_a_141_ = lean_ctor_get(v___x_139_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_156_ == 0)
{
v___x_143_ = v___x_139_;
v_isShared_144_ = v_isSharedCheck_156_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_156_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_145_ = lean_mk_empty_array_with_capacity(v___x_132_);
v___x_146_ = lean_array_push(v___x_145_, v_a_127_);
v___x_147_ = lean_array_push(v___x_146_, v_a_130_);
v___x_148_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_147_);
lean_dec_ref(v___x_147_);
v___x_149_ = l_Lean_Fmt_TaggedDoc_nested(v___x_148_);
v___x_150_ = lean_mk_empty_array_with_capacity(v___x_118_);
v___x_151_ = lean_array_push(v___x_150_, v___x_149_);
v___x_152_ = l_Lean_Fmt_Layouts_alt(v___x_151_, v_a_135_, v_a_140_, v___x_113_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_152_);
v___x_154_ = v___x_143_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_a_141_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
lean_dec(v_a_135_);
lean_dec(v_a_130_);
lean_dec(v_a_127_);
v_a_157_ = lean_ctor_get(v___x_139_, 0);
v_a_158_ = lean_ctor_get(v___x_139_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_139_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_inc(v_a_157_);
lean_dec(v___x_139_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_157_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec(v_a_130_);
lean_dec(v_a_127_);
lean_dec(v_x_109_);
v_a_166_ = lean_ctor_get(v___x_134_, 0);
v_a_167_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_134_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_inc(v_a_166_);
lean_dec(v___x_134_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_166_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_127_);
lean_dec(v_x_109_);
v_a_175_ = lean_ctor_get(v___x_129_, 0);
v_a_176_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_129_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_inc(v_a_175_);
lean_dec(v___x_129_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_175_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec(v___x_119_);
lean_dec(v_x_109_);
v_a_184_ = lean_ctor_get(v___x_126_, 0);
v_a_185_ = lean_ctor_get(v___x_126_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_126_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_inc(v_a_184_);
lean_dec(v___x_126_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_184_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = l_Lean_Syntax_getArg(v_x_109_, v___x_193_);
v___x_195_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlt___closed__8));
lean_inc(v___x_194_);
v___x_196_ = l_Lean_Syntax_isOfKind(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v___x_194_);
lean_dec(v_x_109_);
v___x_197_ = l_Lean_Fmt_Error_partialFormatter;
v___x_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_a_111_);
return v___x_198_;
}
else
{
lean_object* v_cdotTk_199_; lean_object* v___x_200_; 
v_cdotTk_199_ = l_Lean_Syntax_getArg(v___x_194_, v___x_193_);
lean_dec(v___x_194_);
v___x_200_ = l_Lean_Fmt_fmt(v_cdotTk_199_, v_a_110_, v_a_111_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_a_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
v_a_202_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_200_, 2);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = l_Lean_Syntax_getArg(v_x_109_, v___x_203_);
lean_dec(v_x_109_);
v___x_205_ = l_Lean_Fmt_fmt(v___x_204_, v_a_110_, v_a_202_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_226_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_a_207_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_226_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_226_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_226_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_211_ = l_Lean_Fmt_TaggedDoc_aligned(v_a_206_);
v___x_212_ = lean_unsigned_to_nat(2u);
v___x_213_ = lean_mk_empty_array_with_capacity(v___x_212_);
v___x_214_ = lean_array_push(v___x_213_, v_a_201_);
v___x_215_ = lean_array_push(v___x_214_, v___x_211_);
v___x_216_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = l_Lean_Fmt_TaggedDoc_nested(v___x_216_);
v___x_218_ = lean_mk_empty_array_with_capacity(v___x_203_);
v___x_219_ = lean_array_push(v___x_218_, v___x_217_);
v___x_220_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_221_ = 0;
v___x_222_ = l_Lean_Fmt_Layouts_alt(v___x_219_, v___x_220_, v___x_220_, v___x_221_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_222_);
v___x_224_ = v___x_209_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_a_207_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
else
{
lean_object* v_a_227_; lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_a_201_);
v_a_227_ = lean_ctor_get(v___x_205_, 0);
v_a_228_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_205_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_inc(v_a_227_);
lean_dec(v___x_205_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_227_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_x_109_);
v_a_236_ = lean_ctor_get(v___x_200_, 0);
v_a_237_ = lean_ctor_get(v___x_200_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_200_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_inc(v_a_236_);
lean_dec(v___x_200_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_236_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInvariantAlt___boxed(lean_object* v_x_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Fmt_fmtInvariantAlt(v_x_245_, v_a_246_, v_a_247_);
lean_dec_ref(v_a_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__0(size_t v_sz_249_, size_t v_i_250_, lean_object* v_bs_251_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = lean_usize_dec_lt(v_i_250_, v_sz_249_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_bs_251_);
return v___x_253_;
}
else
{
lean_object* v_v_254_; lean_object* v___x_255_; lean_object* v_bs_x27_256_; size_t v___x_257_; size_t v___x_258_; lean_object* v___x_259_; 
v_v_254_ = lean_array_uget(v_bs_251_, v_i_250_);
v___x_255_ = lean_unsigned_to_nat(0u);
v_bs_x27_256_ = lean_array_uset(v_bs_251_, v_i_250_, v___x_255_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_add(v_i_250_, v___x_257_);
v___x_259_ = lean_array_uset(v_bs_x27_256_, v_i_250_, v_v_254_);
v_i_250_ = v___x_258_;
v_bs_251_ = v___x_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__0___boxed(lean_object* v_sz_261_, lean_object* v_i_262_, lean_object* v_bs_263_){
_start:
{
size_t v_sz_boxed_264_; size_t v_i_boxed_265_; lean_object* v_res_266_; 
v_sz_boxed_264_ = lean_unbox_usize(v_sz_261_);
lean_dec(v_sz_261_);
v_i_boxed_265_ = lean_unbox_usize(v_i_262_);
lean_dec(v_i_262_);
v_res_266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__0(v_sz_boxed_264_, v_i_boxed_265_, v_bs_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__1(size_t v_sz_267_, size_t v_i_268_, lean_object* v_bs_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_lt(v_i_268_, v_sz_267_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_bs_269_);
lean_ctor_set(v___x_273_, 1, v___y_271_);
return v___x_273_;
}
else
{
lean_object* v_v_274_; lean_object* v___x_275_; 
v_v_274_ = lean_array_uget_borrowed(v_bs_269_, v_i_268_);
lean_inc(v_v_274_);
v___x_275_ = l_Lean_Fmt_fmtInvariantAlt(v_v_274_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v_bs_x27_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
v_a_277_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_275_, 2);
v___x_278_ = lean_unsigned_to_nat(0u);
v_bs_x27_279_ = lean_array_uset(v_bs_269_, v_i_268_, v___x_278_);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_268_, v___x_280_);
v___x_282_ = lean_array_uset(v_bs_x27_279_, v_i_268_, v_a_276_);
v_i_268_ = v___x_281_;
v_bs_269_ = v___x_282_;
v___y_271_ = v_a_277_;
goto _start;
}
else
{
lean_object* v_a_284_; lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_bs_269_);
v_a_284_ = lean_ctor_get(v___x_275_, 0);
v_a_285_ = lean_ctor_get(v___x_275_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_275_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_inc(v_a_284_);
lean_dec(v___x_275_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_284_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__1___boxed(lean_object* v_sz_293_, lean_object* v_i_294_, lean_object* v_bs_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
size_t v_sz_boxed_298_; size_t v_i_boxed_299_; lean_object* v_res_300_; 
v_sz_boxed_298_ = lean_unbox_usize(v_sz_293_);
lean_dec(v_sz_293_);
v_i_boxed_299_ = lean_unbox_usize(v_i_294_);
lean_dec(v_i_294_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__1(v_sz_boxed_298_, v_i_boxed_299_, v_bs_295_, v___y_296_, v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInvariantAlts(lean_object* v_x_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlts___closed__1));
lean_inc(v_x_313_);
v___x_317_ = l_Lean_Syntax_isOfKind(v_x_313_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_x_313_);
v___x_318_ = l_Lean_Fmt_Error_partialFormatter;
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_a_315_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = l_Lean_Syntax_getArg(v_x_313_, v___x_320_);
v___x_322_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlts___closed__3));
lean_inc(v___x_321_);
v___x_323_ = l_Lean_Syntax_isOfKind(v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v___x_321_);
lean_dec(v_x_313_);
v___x_324_ = l_Lean_Fmt_Error_partialFormatter;
v___x_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_a_315_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; size_t v_sz_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = l_Lean_Syntax_getArg(v_x_313_, v___x_326_);
lean_dec(v_x_313_);
v___x_328_ = l_Lean_Syntax_getArgs(v___x_327_);
lean_dec(v___x_327_);
v_sz_329_ = lean_array_size(v___x_328_);
v___x_330_ = ((size_t)0ULL);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__0(v_sz_329_, v___x_330_, v___x_328_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v___x_321_);
v___x_332_ = l_Lean_Fmt_Error_partialFormatter;
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_a_315_);
return v___x_333_;
}
else
{
lean_object* v_val_334_; lean_object* v___x_335_; 
v_val_334_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v___x_331_, 1);
v___x_335_ = l_Lean_Fmt_fmt(v___x_321_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v_a_337_; size_t v_sz_338_; lean_object* v___x_339_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
v_a_337_ = lean_ctor_get(v___x_335_, 1);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_335_, 2);
v_sz_338_ = lean_array_size(v_val_334_);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInvariantAlts_spec__1(v_sz_338_, v___x_330_, v_val_334_, v_a_314_, v_a_337_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_350_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_a_341_ = lean_ctor_get(v___x_339_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_350_ == 0)
{
v___x_343_ = v___x_339_;
v_isShared_344_ = v_isSharedCheck_350_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_350_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint8_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_345_ = 0;
v___x_346_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_a_336_, v_a_340_, v___x_345_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_346_);
v___x_348_ = v___x_343_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_a_341_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_a_336_);
v_a_351_ = lean_ctor_get(v___x_339_, 0);
v_a_352_ = lean_ctor_get(v___x_339_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_339_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_inc(v_a_351_);
lean_dec(v___x_339_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_351_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_dec(v_val_334_);
return v___x_335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInvariantAlts___boxed(lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Fmt_fmtInvariantAlts(v_x_360_, v_a_361_, v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1(){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_370_ = l_Lean_Fmt_fmtAttribute;
v___x_371_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlts___closed__1));
v___x_372_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___closed__1));
v___x_373_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInvariantAlts___boxed), 3, 0);
v___x_374_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_370_, v___x_371_, v___x_372_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1___boxed(lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1();
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFrameAlt(lean_object* v_x_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Fmt_fmtFrameAlt___closed__1));
lean_inc(v_x_386_);
v___x_390_ = l_Lean_Syntax_isOfKind(v_x_386_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_x_386_);
v___x_391_ = l_Lean_Fmt_Error_partialFormatter;
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_388_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = l_Lean_Syntax_getArg(v_x_386_, v___x_393_);
v___x_395_ = ((lean_object*)(l_Lean_Fmt_fmtFrameAlt___closed__3));
lean_inc(v___x_394_);
v___x_396_ = l_Lean_Syntax_isOfKind(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v___x_394_);
lean_dec(v_x_386_);
v___x_397_ = l_Lean_Fmt_Error_partialFormatter;
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_a_388_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v_pipeTk_400_; lean_object* v___x_401_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v_pipeTk_400_ = l_Lean_Syntax_getArg(v_x_386_, v___x_399_);
v___x_401_ = l_Lean_Fmt_fmt(v_pipeTk_400_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
v_a_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_401_, 2);
v___x_404_ = l_Lean_Fmt_fmt(v___x_394_, v_a_387_, v_a_403_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_args_409_; lean_object* v___x_410_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
v_a_406_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_404_, 2);
v___x_407_ = lean_unsigned_to_nat(2u);
v___x_408_ = l_Lean_Syntax_getArg(v_x_386_, v___x_407_);
v_args_409_ = l_Lean_Syntax_getArgs(v___x_408_);
lean_dec(v___x_408_);
v___x_410_ = l_Lean_Fmt_fmtArray___redArg(v_args_409_, v_a_387_, v_a_406_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v_a_412_; lean_object* v___x_413_; lean_object* v_arrowTk_414_; lean_object* v___x_415_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
v_a_412_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_410_, 2);
v___x_413_ = lean_unsigned_to_nat(3u);
v_arrowTk_414_ = l_Lean_Syntax_getArg(v_x_386_, v___x_413_);
v___x_415_ = l_Lean_Fmt_fmt(v_arrowTk_414_, v_a_387_, v_a_412_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v_a_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
v_a_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_415_, 2);
v___x_418_ = lean_unsigned_to_nat(4u);
v___x_419_ = l_Lean_Syntax_getArg(v_x_386_, v___x_418_);
lean_dec(v_x_386_);
v___x_420_ = l_Lean_Fmt_fmt(v___x_419_, v_a_387_, v_a_417_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_442_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_a_422_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_442_ == 0)
{
v___x_424_ = v___x_420_;
v_isShared_425_ = v_isSharedCheck_442_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_442_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_426_ = lean_mk_empty_array_with_capacity(v___x_393_);
lean_inc_ref(v___x_426_);
v___x_427_ = lean_array_push(v___x_426_, v_a_405_);
v___x_428_ = l_Array_append___redArg(v___x_427_, v_a_411_);
lean_dec(v_a_411_);
v___x_429_ = 0;
v___x_430_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_430_, 0, v___x_396_);
lean_ctor_set_uint8(v___x_430_, 1, v___x_429_);
lean_ctor_set_uint8(v___x_430_, 2, v___x_429_);
lean_ctor_set_uint8(v___x_430_, 3, v___x_429_);
v___x_431_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_428_, v___x_430_);
v___x_432_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_433_ = lean_array_push(v___x_432_, v_a_402_);
v___x_434_ = lean_array_push(v___x_433_, v___x_431_);
v___x_435_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_434_);
lean_dec_ref(v___x_434_);
v___x_436_ = l_Lean_Fmt_TaggedDoc_nested(v___x_435_);
v___x_437_ = lean_array_push(v___x_426_, v___x_436_);
v___x_438_ = l_Lean_Fmt_Layouts_alt(v___x_437_, v_a_416_, v_a_421_, v___x_429_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_438_);
v___x_440_ = v___x_424_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_a_422_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v_a_443_; lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec(v_a_416_);
lean_dec(v_a_411_);
lean_dec(v_a_405_);
lean_dec(v_a_402_);
v_a_443_ = lean_ctor_get(v___x_420_, 0);
v_a_444_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_420_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_inc(v_a_443_);
lean_dec(v___x_420_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_443_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_a_411_);
lean_dec(v_a_405_);
lean_dec(v_a_402_);
lean_dec(v_x_386_);
v_a_452_ = lean_ctor_get(v___x_415_, 0);
v_a_453_ = lean_ctor_get(v___x_415_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_415_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_inc(v_a_452_);
lean_dec(v___x_415_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_452_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_a_405_);
lean_dec(v_a_402_);
lean_dec(v_x_386_);
v_a_461_ = lean_ctor_get(v___x_410_, 0);
v_a_462_ = lean_ctor_get(v___x_410_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_410_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_inc(v_a_461_);
lean_dec(v___x_410_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_461_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec(v_a_402_);
lean_dec(v_x_386_);
v_a_470_ = lean_ctor_get(v___x_404_, 0);
v_a_471_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_404_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_inc(v_a_470_);
lean_dec(v___x_404_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_470_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
else
{
lean_object* v_a_479_; lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v___x_394_);
lean_dec(v_x_386_);
v_a_479_ = lean_ctor_get(v___x_401_, 0);
v_a_480_ = lean_ctor_get(v___x_401_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_401_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_inc(v_a_479_);
lean_dec(v___x_401_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_479_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFrameAlt___boxed(lean_object* v_x_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Fmt_fmtFrameAlt(v_x_488_, v_a_489_, v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenHead_spec__0(size_t v_sz_492_, size_t v_i_493_, lean_object* v_bs_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_bs_494_);
lean_ctor_set(v___x_498_, 1, v___y_496_);
return v___x_498_;
}
else
{
lean_object* v_v_499_; lean_object* v___x_500_; 
v_v_499_ = lean_array_uget_borrowed(v_bs_494_, v_i_493_);
lean_inc(v_v_499_);
v___x_500_ = l_Lean_Fmt_fmt(v_v_499_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v_bs_x27_504_; size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
v_a_502_ = lean_ctor_get(v___x_500_, 1);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_500_, 2);
v___x_503_ = lean_unsigned_to_nat(0u);
v_bs_x27_504_ = lean_array_uset(v_bs_494_, v_i_493_, v___x_503_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_493_, v___x_505_);
v___x_507_ = lean_array_uset(v_bs_x27_504_, v_i_493_, v_a_501_);
v_i_493_ = v___x_506_;
v_bs_494_ = v___x_507_;
v___y_496_ = v_a_502_;
goto _start;
}
else
{
lean_object* v_a_509_; lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_bs_494_);
v_a_509_ = lean_ctor_get(v___x_500_, 0);
v_a_510_ = lean_ctor_get(v___x_500_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_500_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_inc(v_a_509_);
lean_dec(v___x_500_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_509_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenHead_spec__0___boxed(lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_bs_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
size_t v_sz_boxed_523_; size_t v_i_boxed_524_; lean_object* v_res_525_; 
v_sz_boxed_523_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_524_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenHead_spec__0(v_sz_boxed_523_, v_i_boxed_524_, v_bs_520_, v___y_521_, v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenHead(lean_object* v_vcgenTk_529_, lean_object* v_cfg_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Fmt_fmt(v_vcgenTk_529_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
v_a_535_ = lean_ctor_get(v___x_533_, 1);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_533_, 2);
v___x_536_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_530_, v_a_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v_a_538_; size_t v_sz_539_; size_t v___x_540_; lean_object* v___x_541_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
v_a_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_536_, 2);
v_sz_539_ = lean_array_size(v_a_537_);
v___x_540_ = ((size_t)0ULL);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenHead_spec__0(v_sz_539_, v___x_540_, v_a_537_, v_a_531_, v_a_538_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_556_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_a_543_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_556_ == 0)
{
v___x_545_ = v___x_541_;
v_isShared_546_ = v_isSharedCheck_556_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_556_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
v___x_549_ = lean_array_push(v___x_548_, v_a_534_);
v___x_550_ = l_Array_append___redArg(v___x_549_, v_a_542_);
lean_dec(v_a_542_);
v___x_551_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenHead___closed__0));
v___x_552_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_550_, v___x_551_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_552_);
v___x_554_ = v___x_545_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_a_543_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
lean_object* v_a_557_; lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_a_534_);
v_a_557_ = lean_ctor_get(v___x_541_, 0);
v_a_558_ = lean_ctor_get(v___x_541_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_541_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_inc(v_a_557_);
lean_dec(v___x_541_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_557_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_a_534_);
v_a_566_ = lean_ctor_get(v___x_536_, 0);
v_a_567_ = lean_ctor_get(v___x_536_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_536_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_inc(v_a_566_);
lean_dec(v___x_536_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_566_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_dec(v_cfg_530_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenHead___boxed(lean_object* v_vcgenTk_575_, lean_object* v_cfg_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Fmt_fmtVCGenHead(v_vcgenTk_575_, v_cfg_576_, v_a_577_, v_a_578_);
lean_dec_ref(v_a_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenSimpArgs(lean_object* v_lbTk_x3f_586_, lean_object* v_args_x3f_587_, lean_object* v_rbTk_x3f_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Fmt_fmt_x3f(v_lbTk_x3f_586_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___y_596_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
v_a_593_ = lean_ctor_get(v___x_591_, 1);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_591_, 2);
v___x_594_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenSimpArgs___closed__0));
if (lean_obj_tag(v_args_x3f_587_) == 0)
{
lean_object* v___x_621_; 
v___x_621_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenSimpArgs___closed__2));
v___y_596_ = v___x_621_;
goto v___jp_595_;
}
else
{
lean_object* v_val_622_; 
v_val_622_ = lean_ctor_get(v_args_x3f_587_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v_args_x3f_587_, 1);
v___y_596_ = v_val_622_;
goto v___jp_595_;
}
v___jp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Fmt_fmtSepArray___redArg(v___y_596_, v_a_589_, v_a_593_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_600_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
v_a_599_ = lean_ctor_get(v___x_597_, 1);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_597_, 2);
v___x_600_ = l_Lean_Fmt_fmt_x3f(v_rbTk_x3f_588_, v_a_589_, v_a_599_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_611_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_a_602_ = lean_ctor_get(v___x_600_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_611_ == 0)
{
v___x_604_ = v___x_600_;
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenSimpArgs___closed__1));
v___x_607_ = l_Lean_Fmt_Layouts_collection(v___x_594_, v_a_592_, v_a_598_, v_a_601_, v___x_606_);
lean_dec(v_a_598_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_607_);
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_602_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_dec(v_a_598_);
lean_dec(v_a_592_);
return v___x_600_;
}
}
else
{
lean_object* v_a_612_; lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_a_592_);
lean_dec(v_rbTk_x3f_588_);
v_a_612_ = lean_ctor_get(v___x_597_, 0);
v_a_613_ = lean_ctor_get(v___x_597_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_597_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_inc(v_a_612_);
lean_dec(v___x_597_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
else
{
lean_dec(v_rbTk_x3f_588_);
lean_dec(v_args_x3f_587_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenSimpArgs___boxed(lean_object* v_lbTk_x3f_623_, lean_object* v_args_x3f_624_, lean_object* v_rbTk_x3f_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Fmt_fmtVCGenSimpArgs(v_lbTk_x3f_623_, v_args_x3f_624_, v_rbTk_x3f_625_, v_a_626_, v_a_627_);
lean_dec_ref(v_a_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenDischargeGrind(lean_object* v_x_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1));
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
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = l_Lean_Syntax_getArg(v_x_635_, v___x_642_);
lean_dec(v_x_635_);
v___x_644_ = l_Lean_Fmt_fmt(v___x_643_, v_a_636_, v_a_637_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenDischargeGrind___boxed(lean_object* v_x_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Fmt_fmtVCGenDischargeGrind(v_x_645_, v_a_646_, v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1(){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_655_ = l_Lean_Fmt_fmtAttribute;
v___x_656_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenDischargeGrind___closed__1));
v___x_657_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___closed__1));
v___x_658_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtVCGenDischargeGrind___boxed), 3, 0);
v___x_659_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_655_, v___x_656_, v___x_657_, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1___boxed(lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1();
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenDischargeTactic(lean_object* v_x_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1));
lean_inc(v_x_668_);
v___x_672_ = l_Lean_Syntax_isOfKind(v_x_668_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_x_668_);
v___x_673_ = l_Lean_Fmt_Error_partialFormatter;
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v_a_670_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = l_Lean_Syntax_getArg(v_x_668_, v___x_675_);
lean_dec(v_x_668_);
v___x_677_ = l_Lean_Fmt_fmt(v___x_676_, v_a_669_, v_a_670_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenDischargeTactic___boxed(lean_object* v_x_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Fmt_fmtVCGenDischargeTactic(v_x_678_, v_a_679_, v_a_680_);
lean_dec_ref(v_a_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1(){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_688_ = l_Lean_Fmt_fmtAttribute;
v___x_689_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenDischargeTactic___closed__1));
v___x_690_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___closed__1));
v___x_691_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtVCGenDischargeTactic___boxed), 3, 0);
v___x_692_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_688_, v___x_689_, v___x_690_, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1___boxed(lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1();
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenLike_spec__0(size_t v_sz_695_, size_t v_i_696_, lean_object* v_bs_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_lt(v_i_696_, v_sz_695_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_bs_697_);
lean_ctor_set(v___x_701_, 1, v___y_699_);
return v___x_701_;
}
else
{
lean_object* v_v_702_; lean_object* v___x_703_; 
v_v_702_ = lean_array_uget_borrowed(v_bs_697_, v_i_696_);
lean_inc(v_v_702_);
v___x_703_ = l_Lean_Fmt_fmtFrameAlt(v_v_702_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v_bs_x27_707_; size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
v_a_705_ = lean_ctor_get(v___x_703_, 1);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_703_, 2);
v___x_706_ = lean_unsigned_to_nat(0u);
v_bs_x27_707_ = lean_array_uset(v_bs_697_, v_i_696_, v___x_706_);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_696_, v___x_708_);
v___x_710_ = lean_array_uset(v_bs_x27_707_, v_i_696_, v_a_704_);
v_i_696_ = v___x_709_;
v_bs_697_ = v___x_710_;
v___y_699_ = v_a_705_;
goto _start;
}
else
{
lean_object* v_a_712_; lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v_bs_697_);
v_a_712_ = lean_ctor_get(v___x_703_, 0);
v_a_713_ = lean_ctor_get(v___x_703_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_703_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_inc(v_a_712_);
lean_dec(v___x_703_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_712_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenLike_spec__0___boxed(lean_object* v_sz_721_, lean_object* v_i_722_, lean_object* v_bs_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
size_t v_sz_boxed_726_; size_t v_i_boxed_727_; lean_object* v_res_728_; 
v_sz_boxed_726_ = lean_unbox_usize(v_sz_721_);
lean_dec(v_sz_721_);
v_i_boxed_727_ = lean_unbox_usize(v_i_722_);
lean_dec(v_i_722_);
v_res_728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenLike_spec__0(v_sz_boxed_726_, v_i_boxed_727_, v_bs_723_, v___y_724_, v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenLike(lean_object* v_vcgenTk_729_, lean_object* v_cfg_730_, lean_object* v_lbTk_x3f_731_, lean_object* v_args_x3f_732_, lean_object* v_rbTk_x3f_733_, lean_object* v_untilTk_x3f_734_, lean_object* v_untilProgram_x3f_735_, lean_object* v_framesTk_x3f_736_, lean_object* v_frameAlts_737_, lean_object* v_invariantAlts_x3f_738_, lean_object* v_simpTk_x3f_739_, lean_object* v_simpLbTk_x3f_740_, lean_object* v_simpArgs_x3f_741_, lean_object* v_simpRbTk_x3f_742_, lean_object* v_withTk_x3f_743_, lean_object* v_discharge_x3f_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Fmt_fmtVCGenHead(v_vcgenTk_729_, v_cfg_730_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_a_749_; lean_object* v___x_750_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
v_a_749_ = lean_ctor_get(v___x_747_, 1);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_747_, 2);
v___x_750_ = l_Lean_Fmt_fmtVCGenSimpArgs(v_lbTk_x3f_731_, v_args_x3f_732_, v_rbTk_x3f_733_, v_a_745_, v_a_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
v_a_752_ = lean_ctor_get(v___x_750_, 1);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_750_, 2);
v___x_753_ = l_Lean_Fmt_fmt_x3f(v_untilTk_x3f_734_, v_a_745_, v_a_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
v_a_755_ = lean_ctor_get(v___x_753_, 1);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_753_, 2);
v___x_756_ = l_Lean_Fmt_fmt_x3f(v_untilProgram_x3f_735_, v_a_745_, v_a_755_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
v_a_758_ = lean_ctor_get(v___x_756_, 1);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_756_, 2);
v___x_759_ = l_Lean_Fmt_fmt_x3f(v_framesTk_x3f_736_, v_a_745_, v_a_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_a_761_; size_t v_sz_762_; size_t v___x_763_; lean_object* v___x_764_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
v_a_761_ = lean_ctor_get(v___x_759_, 1);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_759_, 2);
v_sz_762_ = lean_array_size(v_frameAlts_737_);
v___x_763_ = ((size_t)0ULL);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGenLike_spec__0(v_sz_762_, v___x_763_, v_frameAlts_737_, v_a_745_, v_a_761_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
v_a_766_ = lean_ctor_get(v___x_764_, 1);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_764_, 2);
v___x_767_ = l_Lean_Fmt_fmt_x3f(v_invariantAlts_x3f_738_, v_a_745_, v_a_766_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
v_a_769_ = lean_ctor_get(v___x_767_, 1);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_767_, 2);
v___x_770_ = l_Lean_Fmt_fmt_x3f(v_simpTk_x3f_739_, v_a_745_, v_a_769_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
v_a_772_ = lean_ctor_get(v___x_770_, 1);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_770_, 2);
v___x_773_ = l_Lean_Fmt_fmt_x3f(v_simpLbTk_x3f_740_, v_a_745_, v_a_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v___y_778_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
v_a_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_773_, 2);
v___x_776_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenSimpArgs___closed__0));
if (lean_obj_tag(v_simpArgs_x3f_741_) == 0)
{
lean_object* v___x_832_; 
v___x_832_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenSimpArgs___closed__2));
v___y_778_ = v___x_832_;
goto v___jp_777_;
}
else
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v_simpArgs_x3f_741_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v_simpArgs_x3f_741_, 1);
v___y_778_ = v_val_833_;
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Fmt_fmtSepArray___redArg(v___y_778_, v_a_745_, v_a_775_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v_a_781_; lean_object* v___x_782_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
v_a_781_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_779_, 2);
v___x_782_ = l_Lean_Fmt_fmt_x3f(v_simpRbTk_x3f_742_, v_a_745_, v_a_781_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
v_a_784_ = lean_ctor_get(v___x_782_, 1);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_782_, 2);
v___x_785_ = l_Lean_Fmt_fmt_x3f(v_withTk_x3f_743_, v_a_745_, v_a_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v_a_787_; lean_object* v___x_788_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
v_a_787_ = lean_ctor_get(v___x_785_, 1);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_785_, 2);
v___x_788_ = l_Lean_Fmt_fmt_x3f(v_discharge_x3f_744_, v_a_745_, v_a_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_822_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_a_790_ = lean_ctor_get(v___x_788_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_822_ == 0)
{
v___x_792_ = v___x_788_;
v_isShared_793_ = v_isSharedCheck_822_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_822_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_794_ = 0;
v___x_795_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_a_754_, v_a_757_, v___x_794_);
v___x_796_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_a_760_, v_a_765_, v___x_794_);
v___x_797_ = 0;
v___x_798_ = 1;
v___x_799_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenSimpArgs___closed__1));
v___x_800_ = l_Lean_Fmt_Layouts_keywordPrefixedCollection(v___x_776_, v_a_771_, v_a_774_, v_a_780_, v_a_783_, v___x_799_);
lean_dec(v_a_780_);
v___x_801_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_a_786_, v_a_789_, v___x_794_);
v___x_802_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_802_, 0, v___x_796_);
lean_ctor_set_uint8(v___x_802_, sizeof(void*)*1, v___x_797_);
v___x_803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_803_, 0, v_a_768_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*1, v___x_797_);
v___x_804_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_804_, 0, v_a_748_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*1, v___x_798_);
v___x_805_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_805_, 0, v_a_751_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*1, v___x_798_);
v___x_806_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_806_, 0, v___x_795_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*1, v___x_798_);
v___x_807_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_807_, 0, v___x_800_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*1, v___x_798_);
v___x_808_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_808_, 0, v___x_801_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*1, v___x_798_);
v___x_809_ = lean_unsigned_to_nat(7u);
v___x_810_ = lean_mk_empty_array_with_capacity(v___x_809_);
v___x_811_ = lean_array_push(v___x_810_, v___x_804_);
v___x_812_ = lean_array_push(v___x_811_, v___x_805_);
v___x_813_ = lean_array_push(v___x_812_, v___x_806_);
v___x_814_ = lean_array_push(v___x_813_, v___x_802_);
v___x_815_ = lean_array_push(v___x_814_, v___x_803_);
v___x_816_ = lean_array_push(v___x_815_, v___x_807_);
v___x_817_ = lean_array_push(v___x_816_, v___x_808_);
v___x_818_ = l_Lean_Fmt_Layouts_blocks(v___x_817_, v___x_798_);
lean_dec_ref(v___x_817_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_818_);
v___x_820_ = v___x_792_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_a_790_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_dec(v_a_786_);
lean_dec(v_a_783_);
lean_dec(v_a_780_);
lean_dec(v_a_774_);
lean_dec(v_a_771_);
lean_dec(v_a_768_);
lean_dec(v_a_765_);
lean_dec(v_a_760_);
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
return v___x_788_;
}
}
else
{
lean_dec(v_a_783_);
lean_dec(v_a_780_);
lean_dec(v_a_774_);
lean_dec(v_a_771_);
lean_dec(v_a_768_);
lean_dec(v_a_765_);
lean_dec(v_a_760_);
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
return v___x_785_;
}
}
else
{
lean_dec(v_a_780_);
lean_dec(v_a_774_);
lean_dec(v_a_771_);
lean_dec(v_a_768_);
lean_dec(v_a_765_);
lean_dec(v_a_760_);
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
return v___x_782_;
}
}
else
{
lean_object* v_a_823_; lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_a_774_);
lean_dec(v_a_771_);
lean_dec(v_a_768_);
lean_dec(v_a_765_);
lean_dec(v_a_760_);
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
v_a_823_ = lean_ctor_get(v___x_779_, 0);
v_a_824_ = lean_ctor_get(v___x_779_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_779_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_inc(v_a_823_);
lean_dec(v___x_779_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_823_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
else
{
lean_dec(v_a_771_);
lean_dec(v_a_768_);
lean_dec(v_a_765_);
lean_dec(v_a_760_);
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
return v___x_773_;
}
}
else
{
lean_dec(v_a_768_);
lean_dec(v_a_765_);
lean_dec(v_a_760_);
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
lean_dec(v_simpLbTk_x3f_740_);
return v___x_770_;
}
}
else
{
lean_dec(v_a_765_);
lean_dec(v_a_760_);
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
lean_dec(v_simpLbTk_x3f_740_);
lean_dec(v_simpTk_x3f_739_);
return v___x_767_;
}
}
else
{
lean_object* v_a_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_a_760_);
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
lean_dec(v_simpLbTk_x3f_740_);
lean_dec(v_simpTk_x3f_739_);
lean_dec(v_invariantAlts_x3f_738_);
v_a_834_ = lean_ctor_get(v___x_764_, 0);
v_a_835_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_764_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_inc(v_a_834_);
lean_dec(v___x_764_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_834_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_dec(v_a_757_);
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
lean_dec(v_simpLbTk_x3f_740_);
lean_dec(v_simpTk_x3f_739_);
lean_dec(v_invariantAlts_x3f_738_);
lean_dec_ref(v_frameAlts_737_);
return v___x_759_;
}
}
else
{
lean_dec(v_a_754_);
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
lean_dec(v_simpLbTk_x3f_740_);
lean_dec(v_simpTk_x3f_739_);
lean_dec(v_invariantAlts_x3f_738_);
lean_dec_ref(v_frameAlts_737_);
lean_dec(v_framesTk_x3f_736_);
return v___x_756_;
}
}
else
{
lean_dec(v_a_751_);
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
lean_dec(v_simpLbTk_x3f_740_);
lean_dec(v_simpTk_x3f_739_);
lean_dec(v_invariantAlts_x3f_738_);
lean_dec_ref(v_frameAlts_737_);
lean_dec(v_framesTk_x3f_736_);
lean_dec(v_untilProgram_x3f_735_);
return v___x_753_;
}
}
else
{
lean_dec(v_a_748_);
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
lean_dec(v_simpLbTk_x3f_740_);
lean_dec(v_simpTk_x3f_739_);
lean_dec(v_invariantAlts_x3f_738_);
lean_dec_ref(v_frameAlts_737_);
lean_dec(v_framesTk_x3f_736_);
lean_dec(v_untilProgram_x3f_735_);
lean_dec(v_untilTk_x3f_734_);
return v___x_750_;
}
}
else
{
lean_dec(v_discharge_x3f_744_);
lean_dec(v_withTk_x3f_743_);
lean_dec(v_simpRbTk_x3f_742_);
lean_dec(v_simpArgs_x3f_741_);
lean_dec(v_simpLbTk_x3f_740_);
lean_dec(v_simpTk_x3f_739_);
lean_dec(v_invariantAlts_x3f_738_);
lean_dec_ref(v_frameAlts_737_);
lean_dec(v_framesTk_x3f_736_);
lean_dec(v_untilProgram_x3f_735_);
lean_dec(v_untilTk_x3f_734_);
lean_dec(v_rbTk_x3f_733_);
lean_dec(v_args_x3f_732_);
lean_dec(v_lbTk_x3f_731_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGenLike___boxed(lean_object** _args){
lean_object* v_vcgenTk_843_ = _args[0];
lean_object* v_cfg_844_ = _args[1];
lean_object* v_lbTk_x3f_845_ = _args[2];
lean_object* v_args_x3f_846_ = _args[3];
lean_object* v_rbTk_x3f_847_ = _args[4];
lean_object* v_untilTk_x3f_848_ = _args[5];
lean_object* v_untilProgram_x3f_849_ = _args[6];
lean_object* v_framesTk_x3f_850_ = _args[7];
lean_object* v_frameAlts_851_ = _args[8];
lean_object* v_invariantAlts_x3f_852_ = _args[9];
lean_object* v_simpTk_x3f_853_ = _args[10];
lean_object* v_simpLbTk_x3f_854_ = _args[11];
lean_object* v_simpArgs_x3f_855_ = _args[12];
lean_object* v_simpRbTk_x3f_856_ = _args[13];
lean_object* v_withTk_x3f_857_ = _args[14];
lean_object* v_discharge_x3f_858_ = _args[15];
lean_object* v_a_859_ = _args[16];
lean_object* v_a_860_ = _args[17];
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Fmt_fmtVCGenLike(v_vcgenTk_843_, v_cfg_844_, v_lbTk_x3f_845_, v_args_x3f_846_, v_rbTk_x3f_847_, v_untilTk_x3f_848_, v_untilProgram_x3f_849_, v_framesTk_x3f_850_, v_frameAlts_851_, v_invariantAlts_x3f_852_, v_simpTk_x3f_853_, v_simpLbTk_x3f_854_, v_simpArgs_x3f_855_, v_simpRbTk_x3f_856_, v_withTk_x3f_857_, v_discharge_x3f_858_, v_a_859_, v_a_860_);
lean_dec_ref(v_a_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGen_spec__0(size_t v_sz_862_, size_t v_i_863_, lean_object* v_bs_864_){
_start:
{
uint8_t v___x_865_; 
v___x_865_ = lean_usize_dec_lt(v_i_863_, v_sz_862_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; 
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v_bs_864_);
return v___x_866_;
}
else
{
lean_object* v_v_867_; lean_object* v___x_868_; lean_object* v_bs_x27_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; 
v_v_867_ = lean_array_uget(v_bs_864_, v_i_863_);
v___x_868_ = lean_unsigned_to_nat(0u);
v_bs_x27_869_ = lean_array_uset(v_bs_864_, v_i_863_, v___x_868_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_863_, v___x_870_);
v___x_872_ = lean_array_uset(v_bs_x27_869_, v_i_863_, v_v_867_);
v_i_863_ = v___x_871_;
v_bs_864_ = v___x_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGen_spec__0___boxed(lean_object* v_sz_874_, lean_object* v_i_875_, lean_object* v_bs_876_){
_start:
{
size_t v_sz_boxed_877_; size_t v_i_boxed_878_; lean_object* v_res_879_; 
v_sz_boxed_877_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v_i_boxed_878_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGen_spec__0(v_sz_boxed_877_, v_i_boxed_878_, v_bs_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGen(lean_object* v_x_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = ((lean_object*)(l_Lean_Fmt_fmtVCGen___closed__1));
lean_inc(v_x_892_);
v___x_896_ = l_Lean_Syntax_isOfKind(v_x_892_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec(v_x_892_);
v___x_897_ = l_Lean_Fmt_Error_partialFormatter;
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_a_894_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v_cfg_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_899_ = lean_unsigned_to_nat(1u);
v_cfg_900_ = l_Lean_Syntax_getArg(v_x_892_, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_Fmt_fmtVCGen___closed__3));
lean_inc(v_cfg_900_);
v___x_902_ = l_Lean_Syntax_isOfKind(v_cfg_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec(v_cfg_900_);
lean_dec(v_x_892_);
v___x_903_ = l_Lean_Fmt_Error_partialFormatter;
v___x_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_a_894_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v_vcgenTk_906_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v_withTk_x3f_1045_; lean_object* v_discharge_x3f_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___x_1058_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v_simpTk_x3f_1068_; lean_object* v_simpLbTk_x3f_1069_; lean_object* v_simpArgs_x3f_1070_; lean_object* v_simpRbTk_x3f_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v_invariantAlts_x3f_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v_framesTk_x3f_1122_; lean_object* v_frameAlts_x3f_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v_untilTk_x3f_1144_; lean_object* v_untilProgram_x3f_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v_lbTk_x3f_1165_; lean_object* v_args_x3f_1166_; lean_object* v_rbTk_x3f_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v_vcgenTk_906_ = l_Lean_Syntax_getArg(v_x_892_, v___x_905_);
v___x_1058_ = lean_unsigned_to_nat(2u);
v___x_1181_ = l_Lean_Syntax_getArg(v_x_892_, v___x_1058_);
v___x_1182_ = l_Lean_Syntax_isNone(v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1181_);
v___x_1184_ = l_Lean_Syntax_matchesNull(v___x_1181_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v___x_1181_);
lean_dec(v_vcgenTk_906_);
lean_dec(v_cfg_900_);
lean_dec(v_x_892_);
v___x_1185_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v_a_894_);
return v___x_1186_;
}
else
{
lean_object* v_lbTk_x3f_1187_; lean_object* v___x_1188_; lean_object* v_rbTk_x3f_1189_; lean_object* v_args_x3f_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_lbTk_x3f_1187_ = l_Lean_Syntax_getArg(v___x_1181_, v___x_905_);
v___x_1188_ = l_Lean_Syntax_getArg(v___x_1181_, v___x_899_);
v_rbTk_x3f_1189_ = l_Lean_Syntax_getArg(v___x_1181_, v___x_1058_);
lean_dec(v___x_1181_);
v_args_x3f_1190_ = l_Lean_Syntax_getArgs(v___x_1188_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_lbTk_x3f_1187_);
v___x_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_args_x3f_1190_);
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_rbTk_x3f_1189_);
v_lbTk_x3f_1165_ = v___x_1191_;
v_args_x3f_1166_ = v___x_1192_;
v_rbTk_x3f_1167_ = v___x_1193_;
v___y_1168_ = v_a_893_;
v___y_1169_ = v_a_894_;
goto v___jp_1164_;
}
}
else
{
lean_object* v___x_1194_; 
lean_dec(v___x_1181_);
v___x_1194_ = lean_box(0);
v_lbTk_x3f_1165_ = v___x_1194_;
v_args_x3f_1166_ = v___x_1194_;
v_rbTk_x3f_1167_ = v___x_1194_;
v___y_1168_ = v_a_893_;
v___y_1169_ = v_a_894_;
goto v___jp_1164_;
}
v___jp_907_:
{
if (lean_obj_tag(v___y_908_) == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_box(0);
v___x_925_ = l_Lean_Fmt_fmtVCGenLike(v_vcgenTk_906_, v_cfg_900_, v___y_914_, v___y_915_, v___y_919_, v___y_921_, v___y_916_, v___y_920_, v___y_910_, v___y_911_, v___y_909_, v___y_912_, v___y_923_, v___y_917_, v___y_913_, v___x_924_, v___y_918_, v___y_922_);
return v___x_925_;
}
else
{
lean_object* v_val_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_934_; 
v_val_926_ = lean_ctor_get(v___y_908_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___y_908_);
if (v_isSharedCheck_934_ == 0)
{
v___x_928_ = v___y_908_;
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_val_926_);
lean_dec(v___y_908_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_val_926_);
v___x_931_ = v_reuseFailAlloc_933_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Fmt_fmtVCGenLike(v_vcgenTk_906_, v_cfg_900_, v___y_914_, v___y_915_, v___y_919_, v___y_921_, v___y_916_, v___y_920_, v___y_910_, v___y_911_, v___y_909_, v___y_912_, v___y_923_, v___y_917_, v___y_913_, v___x_931_, v___y_918_, v___y_922_);
return v___x_932_;
}
}
}
}
v___jp_935_:
{
if (lean_obj_tag(v___y_940_) == 0)
{
lean_object* v___x_952_; 
v___x_952_ = lean_box(0);
v___y_908_ = v___y_936_;
v___y_909_ = v___y_937_;
v___y_910_ = v___y_938_;
v___y_911_ = v___y_951_;
v___y_912_ = v___y_939_;
v___y_913_ = v___y_941_;
v___y_914_ = v___y_942_;
v___y_915_ = v___y_943_;
v___y_916_ = v___y_944_;
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_947_;
v___y_920_ = v___y_948_;
v___y_921_ = v___y_949_;
v___y_922_ = v___y_950_;
v___y_923_ = v___x_952_;
goto v___jp_907_;
}
else
{
lean_object* v_val_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_val_953_ = lean_ctor_get(v___y_940_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___y_940_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___y_940_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_val_953_);
lean_dec(v___y_940_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_val_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
v___y_908_ = v___y_936_;
v___y_909_ = v___y_937_;
v___y_910_ = v___y_938_;
v___y_911_ = v___y_951_;
v___y_912_ = v___y_939_;
v___y_913_ = v___y_941_;
v___y_914_ = v___y_942_;
v___y_915_ = v___y_943_;
v___y_916_ = v___y_944_;
v___y_917_ = v___y_945_;
v___y_918_ = v___y_946_;
v___y_919_ = v___y_947_;
v___y_920_ = v___y_948_;
v___y_921_ = v___y_949_;
v___y_922_ = v___y_950_;
v___y_923_ = v___x_958_;
goto v___jp_907_;
}
}
}
}
v___jp_961_:
{
if (lean_obj_tag(v___y_973_) == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_box(0);
v___y_936_ = v___y_962_;
v___y_937_ = v___y_963_;
v___y_938_ = v___y_977_;
v___y_939_ = v___y_964_;
v___y_940_ = v___y_965_;
v___y_941_ = v___y_966_;
v___y_942_ = v___y_967_;
v___y_943_ = v___y_968_;
v___y_944_ = v___y_969_;
v___y_945_ = v___y_970_;
v___y_946_ = v___y_971_;
v___y_947_ = v___y_972_;
v___y_948_ = v___y_974_;
v___y_949_ = v___y_975_;
v___y_950_ = v___y_976_;
v___y_951_ = v___x_978_;
goto v___jp_935_;
}
else
{
lean_object* v_val_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_val_979_ = lean_ctor_get(v___y_973_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___y_973_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___y_973_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_val_979_);
lean_dec(v___y_973_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_val_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
v___y_936_ = v___y_962_;
v___y_937_ = v___y_963_;
v___y_938_ = v___y_977_;
v___y_939_ = v___y_964_;
v___y_940_ = v___y_965_;
v___y_941_ = v___y_966_;
v___y_942_ = v___y_967_;
v___y_943_ = v___y_968_;
v___y_944_ = v___y_969_;
v___y_945_ = v___y_970_;
v___y_946_ = v___y_971_;
v___y_947_ = v___y_972_;
v___y_948_ = v___y_974_;
v___y_949_ = v___y_975_;
v___y_950_ = v___y_976_;
v___y_951_ = v___x_984_;
goto v___jp_935_;
}
}
}
}
v___jp_987_:
{
if (lean_obj_tag(v___y_996_) == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenSimpArgs___closed__2));
v___y_962_ = v___y_988_;
v___y_963_ = v___y_989_;
v___y_964_ = v___y_990_;
v___y_965_ = v___y_991_;
v___y_966_ = v___y_992_;
v___y_967_ = v___y_993_;
v___y_968_ = v___y_994_;
v___y_969_ = v___y_1003_;
v___y_970_ = v___y_995_;
v___y_971_ = v___y_997_;
v___y_972_ = v___y_998_;
v___y_973_ = v___y_999_;
v___y_974_ = v___y_1000_;
v___y_975_ = v___y_1001_;
v___y_976_ = v___y_1002_;
v___y_977_ = v___x_1004_;
goto v___jp_961_;
}
else
{
lean_object* v_val_1005_; 
v_val_1005_ = lean_ctor_get(v___y_996_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v___y_996_, 1);
v___y_962_ = v___y_988_;
v___y_963_ = v___y_989_;
v___y_964_ = v___y_990_;
v___y_965_ = v___y_991_;
v___y_966_ = v___y_992_;
v___y_967_ = v___y_993_;
v___y_968_ = v___y_994_;
v___y_969_ = v___y_1003_;
v___y_970_ = v___y_995_;
v___y_971_ = v___y_997_;
v___y_972_ = v___y_998_;
v___y_973_ = v___y_999_;
v___y_974_ = v___y_1000_;
v___y_975_ = v___y_1001_;
v___y_976_ = v___y_1002_;
v___y_977_ = v_val_1005_;
goto v___jp_961_;
}
}
v___jp_1006_:
{
if (lean_obj_tag(v___y_1020_) == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_box(0);
v___y_988_ = v___y_1007_;
v___y_989_ = v___y_1008_;
v___y_990_ = v___y_1009_;
v___y_991_ = v___y_1010_;
v___y_992_ = v___y_1011_;
v___y_993_ = v___y_1012_;
v___y_994_ = v___y_1022_;
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1014_;
v___y_997_ = v___y_1015_;
v___y_998_ = v___y_1016_;
v___y_999_ = v___y_1017_;
v___y_1000_ = v___y_1018_;
v___y_1001_ = v___y_1019_;
v___y_1002_ = v___y_1021_;
v___y_1003_ = v___x_1023_;
goto v___jp_987_;
}
else
{
lean_object* v_val_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_val_1024_ = lean_ctor_get(v___y_1020_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___y_1020_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___y_1020_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_val_1024_);
lean_dec(v___y_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_val_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
v___y_988_ = v___y_1007_;
v___y_989_ = v___y_1008_;
v___y_990_ = v___y_1009_;
v___y_991_ = v___y_1010_;
v___y_992_ = v___y_1011_;
v___y_993_ = v___y_1012_;
v___y_994_ = v___y_1022_;
v___y_995_ = v___y_1013_;
v___y_996_ = v___y_1014_;
v___y_997_ = v___y_1015_;
v___y_998_ = v___y_1016_;
v___y_999_ = v___y_1017_;
v___y_1000_ = v___y_1018_;
v___y_1001_ = v___y_1019_;
v___y_1002_ = v___y_1021_;
v___y_1003_ = v___x_1029_;
goto v___jp_987_;
}
}
}
}
v___jp_1032_:
{
if (lean_obj_tag(v___y_1044_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_box(0);
v___y_1007_ = v_discharge_x3f_1046_;
v___y_1008_ = v___y_1033_;
v___y_1009_ = v___y_1037_;
v___y_1010_ = v___y_1041_;
v___y_1011_ = v_withTk_x3f_1045_;
v___y_1012_ = v___y_1034_;
v___y_1013_ = v___y_1035_;
v___y_1014_ = v___y_1036_;
v___y_1015_ = v___y_1047_;
v___y_1016_ = v___y_1038_;
v___y_1017_ = v___y_1040_;
v___y_1018_ = v___y_1039_;
v___y_1019_ = v___y_1042_;
v___y_1020_ = v___y_1043_;
v___y_1021_ = v___y_1048_;
v___y_1022_ = v___x_1049_;
goto v___jp_1006_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_val_1050_ = lean_ctor_get(v___y_1044_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___y_1044_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___y_1044_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_val_1050_);
lean_dec(v___y_1044_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_val_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
v___y_1007_ = v_discharge_x3f_1046_;
v___y_1008_ = v___y_1033_;
v___y_1009_ = v___y_1037_;
v___y_1010_ = v___y_1041_;
v___y_1011_ = v_withTk_x3f_1045_;
v___y_1012_ = v___y_1034_;
v___y_1013_ = v___y_1035_;
v___y_1014_ = v___y_1036_;
v___y_1015_ = v___y_1047_;
v___y_1016_ = v___y_1038_;
v___y_1017_ = v___y_1040_;
v___y_1018_ = v___y_1039_;
v___y_1019_ = v___y_1042_;
v___y_1020_ = v___y_1043_;
v___y_1021_ = v___y_1048_;
v___y_1022_ = v___x_1055_;
goto v___jp_1006_;
}
}
}
}
v___jp_1059_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_unsigned_to_nat(7u);
v___x_1075_ = l_Lean_Syntax_getArg(v_x_892_, v___x_1074_);
lean_dec(v_x_892_);
v___x_1076_ = l_Lean_Syntax_isNone(v___x_1075_);
if (v___x_1076_ == 0)
{
uint8_t v___x_1077_; 
lean_inc(v___x_1075_);
v___x_1077_ = l_Lean_Syntax_matchesNull(v___x_1075_, v___x_1058_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec(v___x_1075_);
lean_dec(v_simpRbTk_x3f_1071_);
lean_dec(v_simpArgs_x3f_1070_);
lean_dec(v_simpLbTk_x3f_1069_);
lean_dec(v_simpTk_x3f_1068_);
lean_dec(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec(v_vcgenTk_906_);
lean_dec(v_cfg_900_);
v___x_1078_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___y_1073_);
return v___x_1079_;
}
else
{
lean_object* v_withTk_x3f_1080_; lean_object* v_discharge_x3f_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_withTk_x3f_1080_ = l_Lean_Syntax_getArg(v___x_1075_, v___x_905_);
v_discharge_x3f_1081_ = l_Lean_Syntax_getArg(v___x_1075_, v___x_899_);
lean_dec(v___x_1075_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_withTk_x3f_1080_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_discharge_x3f_1081_);
v___y_1033_ = v_simpTk_x3f_1068_;
v___y_1034_ = v___y_1060_;
v___y_1035_ = v_simpRbTk_x3f_1071_;
v___y_1036_ = v___y_1061_;
v___y_1037_ = v_simpLbTk_x3f_1069_;
v___y_1038_ = v___y_1062_;
v___y_1039_ = v___y_1064_;
v___y_1040_ = v___y_1063_;
v___y_1041_ = v_simpArgs_x3f_1070_;
v___y_1042_ = v___y_1065_;
v___y_1043_ = v___y_1066_;
v___y_1044_ = v___y_1067_;
v_withTk_x3f_1045_ = v___x_1082_;
v_discharge_x3f_1046_ = v___x_1083_;
v___y_1047_ = v___y_1072_;
v___y_1048_ = v___y_1073_;
goto v___jp_1032_;
}
}
else
{
lean_object* v___x_1084_; 
lean_dec(v___x_1075_);
v___x_1084_ = lean_box(0);
v___y_1033_ = v_simpTk_x3f_1068_;
v___y_1034_ = v___y_1060_;
v___y_1035_ = v_simpRbTk_x3f_1071_;
v___y_1036_ = v___y_1061_;
v___y_1037_ = v_simpLbTk_x3f_1069_;
v___y_1038_ = v___y_1062_;
v___y_1039_ = v___y_1064_;
v___y_1040_ = v___y_1063_;
v___y_1041_ = v_simpArgs_x3f_1070_;
v___y_1042_ = v___y_1065_;
v___y_1043_ = v___y_1066_;
v___y_1044_ = v___y_1067_;
v_withTk_x3f_1045_ = v___x_1084_;
v_discharge_x3f_1046_ = v___x_1084_;
v___y_1047_ = v___y_1072_;
v___y_1048_ = v___y_1073_;
goto v___jp_1032_;
}
}
v___jp_1085_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = lean_unsigned_to_nat(6u);
v___x_1099_ = l_Lean_Syntax_getArg(v_x_892_, v___x_1098_);
v___x_1100_ = l_Lean_Syntax_isNone(v___x_1099_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; 
lean_inc(v___x_1099_);
v___x_1101_ = l_Lean_Syntax_matchesNull(v___x_1099_, v___y_1089_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v___x_1099_);
lean_dec(v_invariantAlts_x3f_1095_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v_vcgenTk_906_);
lean_dec(v_cfg_900_);
lean_dec(v_x_892_);
v___x_1102_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___y_1097_);
return v___x_1103_;
}
else
{
lean_object* v_simpTk_x3f_1104_; lean_object* v_simpLbTk_x3f_1105_; lean_object* v___x_1106_; lean_object* v_simpRbTk_x3f_1107_; lean_object* v_simpArgs_x3f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_simpTk_x3f_1104_ = l_Lean_Syntax_getArg(v___x_1099_, v___x_905_);
v_simpLbTk_x3f_1105_ = l_Lean_Syntax_getArg(v___x_1099_, v___x_899_);
v___x_1106_ = l_Lean_Syntax_getArg(v___x_1099_, v___x_1058_);
v_simpRbTk_x3f_1107_ = l_Lean_Syntax_getArg(v___x_1099_, v___y_1088_);
lean_dec(v___x_1099_);
v_simpArgs_x3f_1108_ = l_Lean_Syntax_getArgs(v___x_1106_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_simpTk_x3f_1104_);
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_simpLbTk_x3f_1105_);
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_simpArgs_x3f_1108_);
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_simpRbTk_x3f_1107_);
v___y_1060_ = v___y_1086_;
v___y_1061_ = v___y_1087_;
v___y_1062_ = v___y_1090_;
v___y_1063_ = v_invariantAlts_x3f_1095_;
v___y_1064_ = v___y_1091_;
v___y_1065_ = v___y_1092_;
v___y_1066_ = v___y_1093_;
v___y_1067_ = v___y_1094_;
v_simpTk_x3f_1068_ = v___x_1109_;
v_simpLbTk_x3f_1069_ = v___x_1110_;
v_simpArgs_x3f_1070_ = v___x_1111_;
v_simpRbTk_x3f_1071_ = v___x_1112_;
v___y_1072_ = v___y_1096_;
v___y_1073_ = v___y_1097_;
goto v___jp_1059_;
}
}
else
{
lean_object* v___x_1113_; 
lean_dec(v___x_1099_);
v___x_1113_ = lean_box(0);
v___y_1060_ = v___y_1086_;
v___y_1061_ = v___y_1087_;
v___y_1062_ = v___y_1090_;
v___y_1063_ = v_invariantAlts_x3f_1095_;
v___y_1064_ = v___y_1091_;
v___y_1065_ = v___y_1092_;
v___y_1066_ = v___y_1093_;
v___y_1067_ = v___y_1094_;
v_simpTk_x3f_1068_ = v___x_1113_;
v_simpLbTk_x3f_1069_ = v___x_1113_;
v_simpArgs_x3f_1070_ = v___x_1113_;
v_simpRbTk_x3f_1071_ = v___x_1113_;
v___y_1072_ = v___y_1096_;
v___y_1073_ = v___y_1097_;
goto v___jp_1059_;
}
}
v___jp_1114_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_unsigned_to_nat(5u);
v___x_1127_ = l_Lean_Syntax_getArg(v_x_892_, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_isNone(v___x_1127_);
if (v___x_1128_ == 0)
{
uint8_t v___x_1129_; 
lean_inc(v___x_1127_);
v___x_1129_ = l_Lean_Syntax_matchesNull(v___x_1127_, v___x_899_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v___x_1127_);
lean_dec(v_frameAlts_x3f_1123_);
lean_dec(v_framesTk_x3f_1122_);
lean_dec(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec(v___y_1115_);
lean_dec(v_vcgenTk_906_);
lean_dec(v_cfg_900_);
lean_dec(v_x_892_);
v___x_1130_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___y_1125_);
return v___x_1131_;
}
else
{
lean_object* v_invariantAlts_x3f_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_invariantAlts_x3f_1132_ = l_Lean_Syntax_getArg(v___x_1127_, v___x_905_);
lean_dec(v___x_1127_);
v___x_1133_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlts___closed__1));
lean_inc(v_invariantAlts_x3f_1132_);
v___x_1134_ = l_Lean_Syntax_isOfKind(v_invariantAlts_x3f_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_invariantAlts_x3f_1132_);
lean_dec(v_frameAlts_x3f_1123_);
lean_dec(v_framesTk_x3f_1122_);
lean_dec(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec(v___y_1115_);
lean_dec(v_vcgenTk_906_);
lean_dec(v_cfg_900_);
lean_dec(v_x_892_);
v___x_1135_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___y_1125_);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_invariantAlts_x3f_1132_);
v___y_1086_ = v___y_1115_;
v___y_1087_ = v_frameAlts_x3f_1123_;
v___y_1088_ = v___y_1116_;
v___y_1089_ = v___y_1117_;
v___y_1090_ = v___y_1118_;
v___y_1091_ = v_framesTk_x3f_1122_;
v___y_1092_ = v___y_1119_;
v___y_1093_ = v___y_1120_;
v___y_1094_ = v___y_1121_;
v_invariantAlts_x3f_1095_ = v___x_1137_;
v___y_1096_ = v___y_1124_;
v___y_1097_ = v___y_1125_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v___x_1138_; 
lean_dec(v___x_1127_);
v___x_1138_ = lean_box(0);
v___y_1086_ = v___y_1115_;
v___y_1087_ = v_frameAlts_x3f_1123_;
v___y_1088_ = v___y_1116_;
v___y_1089_ = v___y_1117_;
v___y_1090_ = v___y_1118_;
v___y_1091_ = v_framesTk_x3f_1122_;
v___y_1092_ = v___y_1119_;
v___y_1093_ = v___y_1120_;
v___y_1094_ = v___y_1121_;
v_invariantAlts_x3f_1095_ = v___x_1138_;
v___y_1096_ = v___y_1124_;
v___y_1097_ = v___y_1125_;
goto v___jp_1085_;
}
}
v___jp_1139_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = lean_unsigned_to_nat(4u);
v___x_1149_ = l_Lean_Syntax_getArg(v_x_892_, v___x_1148_);
v___x_1150_ = l_Lean_Syntax_isNone(v___x_1149_);
if (v___x_1150_ == 0)
{
uint8_t v___x_1151_; 
lean_inc(v___x_1149_);
v___x_1151_ = l_Lean_Syntax_matchesNull(v___x_1149_, v___x_1058_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v___x_1149_);
lean_dec(v_untilProgram_x3f_1145_);
lean_dec(v_untilTk_x3f_1144_);
lean_dec(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec(v___y_1140_);
lean_dec(v_vcgenTk_906_);
lean_dec(v_cfg_900_);
lean_dec(v_x_892_);
v___x_1152_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v___y_1147_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; size_t v_sz_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1154_ = l_Lean_Syntax_getArg(v___x_1149_, v___x_899_);
v___x_1155_ = l_Lean_Syntax_getArgs(v___x_1154_);
lean_dec(v___x_1154_);
v_sz_1156_ = lean_array_size(v___x_1155_);
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGen_spec__0(v_sz_1156_, v___x_1157_, v___x_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec(v___x_1149_);
lean_dec(v_untilProgram_x3f_1145_);
lean_dec(v_untilTk_x3f_1144_);
lean_dec(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec(v___y_1140_);
lean_dec(v_vcgenTk_906_);
lean_dec(v_cfg_900_);
lean_dec(v_x_892_);
v___x_1159_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___y_1147_);
return v___x_1160_;
}
else
{
lean_object* v_framesTk_x3f_1161_; lean_object* v___x_1162_; 
v_framesTk_x3f_1161_ = l_Lean_Syntax_getArg(v___x_1149_, v___x_905_);
lean_dec(v___x_1149_);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_framesTk_x3f_1161_);
v___y_1115_ = v___y_1140_;
v___y_1116_ = v___y_1141_;
v___y_1117_ = v___x_1148_;
v___y_1118_ = v___y_1142_;
v___y_1119_ = v_untilTk_x3f_1144_;
v___y_1120_ = v_untilProgram_x3f_1145_;
v___y_1121_ = v___y_1143_;
v_framesTk_x3f_1122_ = v___x_1162_;
v_frameAlts_x3f_1123_ = v___x_1158_;
v___y_1124_ = v___y_1146_;
v___y_1125_ = v___y_1147_;
goto v___jp_1114_;
}
}
}
else
{
lean_object* v___x_1163_; 
lean_dec(v___x_1149_);
v___x_1163_ = lean_box(0);
v___y_1115_ = v___y_1140_;
v___y_1116_ = v___y_1141_;
v___y_1117_ = v___x_1148_;
v___y_1118_ = v___y_1142_;
v___y_1119_ = v_untilTk_x3f_1144_;
v___y_1120_ = v_untilProgram_x3f_1145_;
v___y_1121_ = v___y_1143_;
v_framesTk_x3f_1122_ = v___x_1163_;
v_frameAlts_x3f_1123_ = v___x_1163_;
v___y_1124_ = v___y_1146_;
v___y_1125_ = v___y_1147_;
goto v___jp_1114_;
}
}
v___jp_1164_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1170_ = lean_unsigned_to_nat(3u);
v___x_1171_ = l_Lean_Syntax_getArg(v_x_892_, v___x_1170_);
v___x_1172_ = l_Lean_Syntax_isNone(v___x_1171_);
if (v___x_1172_ == 0)
{
uint8_t v___x_1173_; 
lean_inc(v___x_1171_);
v___x_1173_ = l_Lean_Syntax_matchesNull(v___x_1171_, v___x_1058_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec(v___x_1171_);
lean_dec(v_rbTk_x3f_1167_);
lean_dec(v_args_x3f_1166_);
lean_dec(v_lbTk_x3f_1165_);
lean_dec(v_vcgenTk_906_);
lean_dec(v_cfg_900_);
lean_dec(v_x_892_);
v___x_1174_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v___y_1169_);
return v___x_1175_;
}
else
{
lean_object* v_untilTk_x3f_1176_; lean_object* v_untilProgram_x3f_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_untilTk_x3f_1176_ = l_Lean_Syntax_getArg(v___x_1171_, v___x_905_);
v_untilProgram_x3f_1177_ = l_Lean_Syntax_getArg(v___x_1171_, v___x_899_);
lean_dec(v___x_1171_);
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_untilTk_x3f_1176_);
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_untilProgram_x3f_1177_);
v___y_1140_ = v_lbTk_x3f_1165_;
v___y_1141_ = v___x_1170_;
v___y_1142_ = v_rbTk_x3f_1167_;
v___y_1143_ = v_args_x3f_1166_;
v_untilTk_x3f_1144_ = v___x_1178_;
v_untilProgram_x3f_1145_ = v___x_1179_;
v___y_1146_ = v___y_1168_;
v___y_1147_ = v___y_1169_;
goto v___jp_1139_;
}
}
else
{
lean_object* v___x_1180_; 
lean_dec(v___x_1171_);
v___x_1180_ = lean_box(0);
v___y_1140_ = v_lbTk_x3f_1165_;
v___y_1141_ = v___x_1170_;
v___y_1142_ = v_rbTk_x3f_1167_;
v___y_1143_ = v_args_x3f_1166_;
v_untilTk_x3f_1144_ = v___x_1180_;
v_untilProgram_x3f_1145_ = v___x_1180_;
v___y_1146_ = v___y_1168_;
v___y_1147_ = v___y_1169_;
goto v___jp_1139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVCGen___boxed(lean_object* v_x_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Fmt_fmtVCGen(v_x_1195_, v_a_1196_, v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1(){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1205_ = l_Lean_Fmt_fmtAttribute;
v___x_1206_ = ((lean_object*)(l_Lean_Fmt_fmtVCGen___closed__1));
v___x_1207_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___closed__1));
v___x_1208_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtVCGen___boxed), 3, 0);
v___x_1209_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1205_, v___x_1206_, v___x_1207_, v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1___boxed(lean_object* v_a_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1();
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindVCGen(lean_object* v_x_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_Lean_Fmt_fmtGrindVCGen___closed__1));
lean_inc(v_x_1219_);
v___x_1223_ = l_Lean_Syntax_isOfKind(v_x_1219_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec(v_x_1219_);
v___x_1224_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_a_1221_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; lean_object* v_cfg_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1226_ = lean_unsigned_to_nat(1u);
v_cfg_1227_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Lean_Fmt_fmtVCGen___closed__3));
lean_inc(v_cfg_1227_);
v___x_1229_ = l_Lean_Syntax_isOfKind(v_cfg_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v_cfg_1227_);
lean_dec(v_x_1219_);
v___x_1230_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_a_1221_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v_vcgenTk_1233_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v_simpTk_x3f_1349_; lean_object* v_simpLbTk_x3f_1350_; lean_object* v_simpArgs_x3f_1351_; lean_object* v_simpRbTk_x3f_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___x_1364_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v_invariantAlts_x3f_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v_framesTk_x3f_1402_; lean_object* v_frameAlts_x3f_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v_untilTk_x3f_1424_; lean_object* v_untilProgram_x3f_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v_lbTk_x3f_1445_; lean_object* v_args_x3f_1446_; lean_object* v_rbTk_x3f_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1232_ = lean_unsigned_to_nat(0u);
v_vcgenTk_1233_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1232_);
v___x_1364_ = lean_unsigned_to_nat(2u);
v___x_1461_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1364_);
v___x_1462_ = l_Lean_Syntax_isNone(v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1461_);
v___x_1464_ = l_Lean_Syntax_matchesNull(v___x_1461_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v___x_1461_);
lean_dec(v_vcgenTk_1233_);
lean_dec(v_cfg_1227_);
lean_dec(v_x_1219_);
v___x_1465_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v_a_1221_);
return v___x_1466_;
}
else
{
lean_object* v_lbTk_x3f_1467_; lean_object* v___x_1468_; lean_object* v_rbTk_x3f_1469_; lean_object* v_args_x3f_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_lbTk_x3f_1467_ = l_Lean_Syntax_getArg(v___x_1461_, v___x_1232_);
v___x_1468_ = l_Lean_Syntax_getArg(v___x_1461_, v___x_1226_);
v_rbTk_x3f_1469_ = l_Lean_Syntax_getArg(v___x_1461_, v___x_1364_);
lean_dec(v___x_1461_);
v_args_x3f_1470_ = l_Lean_Syntax_getArgs(v___x_1468_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_lbTk_x3f_1467_);
v___x_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_args_x3f_1470_);
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_rbTk_x3f_1469_);
v_lbTk_x3f_1445_ = v___x_1471_;
v_args_x3f_1446_ = v___x_1472_;
v_rbTk_x3f_1447_ = v___x_1473_;
v___y_1448_ = v_a_1220_;
v___y_1449_ = v_a_1221_;
goto v___jp_1444_;
}
}
else
{
lean_object* v___x_1474_; 
lean_dec(v___x_1461_);
v___x_1474_ = lean_box(0);
v_lbTk_x3f_1445_ = v___x_1474_;
v_args_x3f_1446_ = v___x_1474_;
v_rbTk_x3f_1447_ = v___x_1474_;
v___y_1448_ = v_a_1220_;
v___y_1449_ = v_a_1221_;
goto v___jp_1444_;
}
v___jp_1234_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = l_Lean_Fmt_fmtVCGenLike(v_vcgenTk_1233_, v_cfg_1227_, v___y_1239_, v___y_1238_, v___y_1243_, v___y_1235_, v___y_1244_, v___y_1247_, v___y_1240_, v___y_1241_, v___y_1245_, v___y_1246_, v___y_1248_, v___y_1237_, v___x_1249_, v___x_1249_, v___y_1236_, v___y_1242_);
return v___x_1250_;
}
v___jp_1251_:
{
if (lean_obj_tag(v___y_1263_) == 0)
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_box(0);
v___y_1235_ = v___y_1252_;
v___y_1236_ = v___y_1253_;
v___y_1237_ = v___y_1254_;
v___y_1238_ = v___y_1255_;
v___y_1239_ = v___y_1256_;
v___y_1240_ = v___y_1257_;
v___y_1241_ = v___y_1265_;
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1259_;
v___y_1244_ = v___y_1260_;
v___y_1245_ = v___y_1261_;
v___y_1246_ = v___y_1262_;
v___y_1247_ = v___y_1264_;
v___y_1248_ = v___x_1266_;
goto v___jp_1234_;
}
else
{
lean_object* v_val_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_val_1267_ = lean_ctor_get(v___y_1263_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___y_1263_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___y_1263_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_val_1267_);
lean_dec(v___y_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_val_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
v___y_1235_ = v___y_1252_;
v___y_1236_ = v___y_1253_;
v___y_1237_ = v___y_1254_;
v___y_1238_ = v___y_1255_;
v___y_1239_ = v___y_1256_;
v___y_1240_ = v___y_1257_;
v___y_1241_ = v___y_1265_;
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1259_;
v___y_1244_ = v___y_1260_;
v___y_1245_ = v___y_1261_;
v___y_1246_ = v___y_1262_;
v___y_1247_ = v___y_1264_;
v___y_1248_ = v___x_1272_;
goto v___jp_1234_;
}
}
}
}
v___jp_1275_:
{
if (lean_obj_tag(v___y_1285_) == 0)
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_box(0);
v___y_1252_ = v___y_1276_;
v___y_1253_ = v___y_1277_;
v___y_1254_ = v___y_1278_;
v___y_1255_ = v___y_1279_;
v___y_1256_ = v___y_1280_;
v___y_1257_ = v___y_1289_;
v___y_1258_ = v___y_1281_;
v___y_1259_ = v___y_1282_;
v___y_1260_ = v___y_1283_;
v___y_1261_ = v___y_1284_;
v___y_1262_ = v___y_1286_;
v___y_1263_ = v___y_1287_;
v___y_1264_ = v___y_1288_;
v___y_1265_ = v___x_1290_;
goto v___jp_1251_;
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_val_1291_ = lean_ctor_get(v___y_1285_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___y_1285_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___y_1285_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v___y_1285_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_val_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
v___y_1252_ = v___y_1276_;
v___y_1253_ = v___y_1277_;
v___y_1254_ = v___y_1278_;
v___y_1255_ = v___y_1279_;
v___y_1256_ = v___y_1280_;
v___y_1257_ = v___y_1289_;
v___y_1258_ = v___y_1281_;
v___y_1259_ = v___y_1282_;
v___y_1260_ = v___y_1283_;
v___y_1261_ = v___y_1284_;
v___y_1262_ = v___y_1286_;
v___y_1263_ = v___y_1287_;
v___y_1264_ = v___y_1288_;
v___y_1265_ = v___x_1296_;
goto v___jp_1251_;
}
}
}
}
v___jp_1299_:
{
if (lean_obj_tag(v___y_1305_) == 0)
{
lean_object* v___x_1314_; 
v___x_1314_ = ((lean_object*)(l_Lean_Fmt_fmtVCGenSimpArgs___closed__2));
v___y_1276_ = v___y_1300_;
v___y_1277_ = v___y_1301_;
v___y_1278_ = v___y_1302_;
v___y_1279_ = v___y_1303_;
v___y_1280_ = v___y_1304_;
v___y_1281_ = v___y_1306_;
v___y_1282_ = v___y_1307_;
v___y_1283_ = v___y_1313_;
v___y_1284_ = v___y_1308_;
v___y_1285_ = v___y_1309_;
v___y_1286_ = v___y_1310_;
v___y_1287_ = v___y_1311_;
v___y_1288_ = v___y_1312_;
v___y_1289_ = v___x_1314_;
goto v___jp_1275_;
}
else
{
lean_object* v_val_1315_; 
v_val_1315_ = lean_ctor_get(v___y_1305_, 0);
lean_inc(v_val_1315_);
lean_dec_ref_known(v___y_1305_, 1);
v___y_1276_ = v___y_1300_;
v___y_1277_ = v___y_1301_;
v___y_1278_ = v___y_1302_;
v___y_1279_ = v___y_1303_;
v___y_1280_ = v___y_1304_;
v___y_1281_ = v___y_1306_;
v___y_1282_ = v___y_1307_;
v___y_1283_ = v___y_1313_;
v___y_1284_ = v___y_1308_;
v___y_1285_ = v___y_1309_;
v___y_1286_ = v___y_1310_;
v___y_1287_ = v___y_1311_;
v___y_1288_ = v___y_1312_;
v___y_1289_ = v_val_1315_;
goto v___jp_1275_;
}
}
v___jp_1316_:
{
if (lean_obj_tag(v___y_1320_) == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_box(0);
v___y_1300_ = v___y_1317_;
v___y_1301_ = v___y_1318_;
v___y_1302_ = v___y_1319_;
v___y_1303_ = v___y_1330_;
v___y_1304_ = v___y_1321_;
v___y_1305_ = v___y_1322_;
v___y_1306_ = v___y_1323_;
v___y_1307_ = v___y_1324_;
v___y_1308_ = v___y_1325_;
v___y_1309_ = v___y_1326_;
v___y_1310_ = v___y_1327_;
v___y_1311_ = v___y_1328_;
v___y_1312_ = v___y_1329_;
v___y_1313_ = v___x_1331_;
goto v___jp_1299_;
}
else
{
lean_object* v_val_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_val_1332_ = lean_ctor_get(v___y_1320_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___y_1320_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___y_1320_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_val_1332_);
lean_dec(v___y_1320_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_val_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
v___y_1300_ = v___y_1317_;
v___y_1301_ = v___y_1318_;
v___y_1302_ = v___y_1319_;
v___y_1303_ = v___y_1330_;
v___y_1304_ = v___y_1321_;
v___y_1305_ = v___y_1322_;
v___y_1306_ = v___y_1323_;
v___y_1307_ = v___y_1324_;
v___y_1308_ = v___y_1325_;
v___y_1309_ = v___y_1326_;
v___y_1310_ = v___y_1327_;
v___y_1311_ = v___y_1328_;
v___y_1312_ = v___y_1329_;
v___y_1313_ = v___x_1337_;
goto v___jp_1299_;
}
}
}
}
v___jp_1340_:
{
if (lean_obj_tag(v___y_1343_) == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_box(0);
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1353_;
v___y_1319_ = v_simpRbTk_x3f_1352_;
v___y_1320_ = v___y_1346_;
v___y_1321_ = v___y_1348_;
v___y_1322_ = v___y_1341_;
v___y_1323_ = v___y_1354_;
v___y_1324_ = v___y_1345_;
v___y_1325_ = v_simpTk_x3f_1349_;
v___y_1326_ = v___y_1344_;
v___y_1327_ = v_simpLbTk_x3f_1350_;
v___y_1328_ = v_simpArgs_x3f_1351_;
v___y_1329_ = v___y_1347_;
v___y_1330_ = v___x_1355_;
goto v___jp_1316_;
}
else
{
lean_object* v_val_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_val_1356_ = lean_ctor_get(v___y_1343_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___y_1343_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___y_1343_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_val_1356_);
lean_dec(v___y_1343_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_val_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1353_;
v___y_1319_ = v_simpRbTk_x3f_1352_;
v___y_1320_ = v___y_1346_;
v___y_1321_ = v___y_1348_;
v___y_1322_ = v___y_1341_;
v___y_1323_ = v___y_1354_;
v___y_1324_ = v___y_1345_;
v___y_1325_ = v_simpTk_x3f_1349_;
v___y_1326_ = v___y_1344_;
v___y_1327_ = v_simpLbTk_x3f_1350_;
v___y_1328_ = v_simpArgs_x3f_1351_;
v___y_1329_ = v___y_1347_;
v___y_1330_ = v___x_1361_;
goto v___jp_1316_;
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1378_ = lean_unsigned_to_nat(6u);
v___x_1379_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1378_);
lean_dec(v_x_1219_);
v___x_1380_ = l_Lean_Syntax_isNone(v___x_1379_);
if (v___x_1380_ == 0)
{
uint8_t v___x_1381_; 
lean_inc(v___x_1379_);
v___x_1381_ = l_Lean_Syntax_matchesNull(v___x_1379_, v___y_1369_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v___x_1379_);
lean_dec(v_invariantAlts_x3f_1375_);
lean_dec(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec(v_vcgenTk_1233_);
lean_dec(v_cfg_1227_);
v___x_1382_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___y_1377_);
return v___x_1383_;
}
else
{
lean_object* v_simpTk_x3f_1384_; lean_object* v_simpLbTk_x3f_1385_; lean_object* v___x_1386_; lean_object* v_simpRbTk_x3f_1387_; lean_object* v_simpArgs_x3f_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_simpTk_x3f_1384_ = l_Lean_Syntax_getArg(v___x_1379_, v___x_1232_);
v_simpLbTk_x3f_1385_ = l_Lean_Syntax_getArg(v___x_1379_, v___x_1226_);
v___x_1386_ = l_Lean_Syntax_getArg(v___x_1379_, v___x_1364_);
v_simpRbTk_x3f_1387_ = l_Lean_Syntax_getArg(v___x_1379_, v___y_1374_);
lean_dec(v___x_1379_);
v_simpArgs_x3f_1388_ = l_Lean_Syntax_getArgs(v___x_1386_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_simpTk_x3f_1384_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_simpLbTk_x3f_1385_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v_simpArgs_x3f_1388_);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_simpRbTk_x3f_1387_);
v___y_1341_ = v___y_1366_;
v___y_1342_ = v___y_1367_;
v___y_1343_ = v___y_1368_;
v___y_1344_ = v_invariantAlts_x3f_1375_;
v___y_1345_ = v___y_1370_;
v___y_1346_ = v___y_1371_;
v___y_1347_ = v___y_1373_;
v___y_1348_ = v___y_1372_;
v_simpTk_x3f_1349_ = v___x_1389_;
v_simpLbTk_x3f_1350_ = v___x_1390_;
v_simpArgs_x3f_1351_ = v___x_1391_;
v_simpRbTk_x3f_1352_ = v___x_1392_;
v___y_1353_ = v___y_1376_;
v___y_1354_ = v___y_1377_;
goto v___jp_1340_;
}
}
else
{
lean_object* v___x_1393_; 
lean_dec(v___x_1379_);
v___x_1393_ = lean_box(0);
v___y_1341_ = v___y_1366_;
v___y_1342_ = v___y_1367_;
v___y_1343_ = v___y_1368_;
v___y_1344_ = v_invariantAlts_x3f_1375_;
v___y_1345_ = v___y_1370_;
v___y_1346_ = v___y_1371_;
v___y_1347_ = v___y_1373_;
v___y_1348_ = v___y_1372_;
v_simpTk_x3f_1349_ = v___x_1393_;
v_simpLbTk_x3f_1350_ = v___x_1393_;
v_simpArgs_x3f_1351_ = v___x_1393_;
v_simpRbTk_x3f_1352_ = v___x_1393_;
v___y_1353_ = v___y_1376_;
v___y_1354_ = v___y_1377_;
goto v___jp_1340_;
}
}
v___jp_1394_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1406_ = lean_unsigned_to_nat(5u);
v___x_1407_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1406_);
v___x_1408_ = l_Lean_Syntax_isNone(v___x_1407_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; 
lean_inc(v___x_1407_);
v___x_1409_ = l_Lean_Syntax_matchesNull(v___x_1407_, v___x_1226_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec(v___x_1407_);
lean_dec(v_frameAlts_x3f_1403_);
lean_dec(v_framesTk_x3f_1402_);
lean_dec(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec(v_vcgenTk_1233_);
lean_dec(v_cfg_1227_);
lean_dec(v_x_1219_);
v___x_1410_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___y_1405_);
return v___x_1411_;
}
else
{
lean_object* v_invariantAlts_x3f_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_invariantAlts_x3f_1412_ = l_Lean_Syntax_getArg(v___x_1407_, v___x_1232_);
lean_dec(v___x_1407_);
v___x_1413_ = ((lean_object*)(l_Lean_Fmt_fmtInvariantAlts___closed__1));
lean_inc(v_invariantAlts_x3f_1412_);
v___x_1414_ = l_Lean_Syntax_isOfKind(v_invariantAlts_x3f_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec(v_invariantAlts_x3f_1412_);
lean_dec(v_frameAlts_x3f_1403_);
lean_dec(v_framesTk_x3f_1402_);
lean_dec(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec(v_vcgenTk_1233_);
lean_dec(v_cfg_1227_);
lean_dec(v_x_1219_);
v___x_1415_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v___y_1405_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_invariantAlts_x3f_1412_);
v___y_1366_ = v_frameAlts_x3f_1403_;
v___y_1367_ = v___y_1395_;
v___y_1368_ = v___y_1396_;
v___y_1369_ = v___y_1397_;
v___y_1370_ = v___y_1398_;
v___y_1371_ = v___y_1399_;
v___y_1372_ = v___y_1400_;
v___y_1373_ = v_framesTk_x3f_1402_;
v___y_1374_ = v___y_1401_;
v_invariantAlts_x3f_1375_ = v___x_1417_;
v___y_1376_ = v___y_1404_;
v___y_1377_ = v___y_1405_;
goto v___jp_1365_;
}
}
}
else
{
lean_object* v___x_1418_; 
lean_dec(v___x_1407_);
v___x_1418_ = lean_box(0);
v___y_1366_ = v_frameAlts_x3f_1403_;
v___y_1367_ = v___y_1395_;
v___y_1368_ = v___y_1396_;
v___y_1369_ = v___y_1397_;
v___y_1370_ = v___y_1398_;
v___y_1371_ = v___y_1399_;
v___y_1372_ = v___y_1400_;
v___y_1373_ = v_framesTk_x3f_1402_;
v___y_1374_ = v___y_1401_;
v_invariantAlts_x3f_1375_ = v___x_1418_;
v___y_1376_ = v___y_1404_;
v___y_1377_ = v___y_1405_;
goto v___jp_1365_;
}
}
v___jp_1419_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_unsigned_to_nat(4u);
v___x_1429_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1428_);
v___x_1430_ = l_Lean_Syntax_isNone(v___x_1429_);
if (v___x_1430_ == 0)
{
uint8_t v___x_1431_; 
lean_inc(v___x_1429_);
v___x_1431_ = l_Lean_Syntax_matchesNull(v___x_1429_, v___x_1364_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v___x_1429_);
lean_dec(v_untilProgram_x3f_1425_);
lean_dec(v_untilTk_x3f_1424_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec(v_vcgenTk_1233_);
lean_dec(v_cfg_1227_);
lean_dec(v_x_1219_);
v___x_1432_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___y_1427_);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; size_t v_sz_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1434_ = l_Lean_Syntax_getArg(v___x_1429_, v___x_1226_);
v___x_1435_ = l_Lean_Syntax_getArgs(v___x_1434_);
lean_dec(v___x_1434_);
v_sz_1436_ = lean_array_size(v___x_1435_);
v___x_1437_ = ((size_t)0ULL);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtVCGen_spec__0(v_sz_1436_, v___x_1437_, v___x_1435_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec(v___x_1429_);
lean_dec(v_untilProgram_x3f_1425_);
lean_dec(v_untilTk_x3f_1424_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec(v_vcgenTk_1233_);
lean_dec(v_cfg_1227_);
lean_dec(v_x_1219_);
v___x_1439_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v___y_1427_);
return v___x_1440_;
}
else
{
lean_object* v_framesTk_x3f_1441_; lean_object* v___x_1442_; 
v_framesTk_x3f_1441_ = l_Lean_Syntax_getArg(v___x_1429_, v___x_1232_);
lean_dec(v___x_1429_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_framesTk_x3f_1441_);
v___y_1395_ = v_untilTk_x3f_1424_;
v___y_1396_ = v___y_1420_;
v___y_1397_ = v___x_1428_;
v___y_1398_ = v___y_1421_;
v___y_1399_ = v_untilProgram_x3f_1425_;
v___y_1400_ = v___y_1422_;
v___y_1401_ = v___y_1423_;
v_framesTk_x3f_1402_ = v___x_1442_;
v_frameAlts_x3f_1403_ = v___x_1438_;
v___y_1404_ = v___y_1426_;
v___y_1405_ = v___y_1427_;
goto v___jp_1394_;
}
}
}
else
{
lean_object* v___x_1443_; 
lean_dec(v___x_1429_);
v___x_1443_ = lean_box(0);
v___y_1395_ = v_untilTk_x3f_1424_;
v___y_1396_ = v___y_1420_;
v___y_1397_ = v___x_1428_;
v___y_1398_ = v___y_1421_;
v___y_1399_ = v_untilProgram_x3f_1425_;
v___y_1400_ = v___y_1422_;
v___y_1401_ = v___y_1423_;
v_framesTk_x3f_1402_ = v___x_1443_;
v_frameAlts_x3f_1403_ = v___x_1443_;
v___y_1404_ = v___y_1426_;
v___y_1405_ = v___y_1427_;
goto v___jp_1394_;
}
}
v___jp_1444_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = lean_unsigned_to_nat(3u);
v___x_1451_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1450_);
v___x_1452_ = l_Lean_Syntax_isNone(v___x_1451_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; 
lean_inc(v___x_1451_);
v___x_1453_ = l_Lean_Syntax_matchesNull(v___x_1451_, v___x_1364_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec(v___x_1451_);
lean_dec(v_rbTk_x3f_1447_);
lean_dec(v_args_x3f_1446_);
lean_dec(v_lbTk_x3f_1445_);
lean_dec(v_vcgenTk_1233_);
lean_dec(v_cfg_1227_);
lean_dec(v_x_1219_);
v___x_1454_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___y_1449_);
return v___x_1455_;
}
else
{
lean_object* v_untilTk_x3f_1456_; lean_object* v_untilProgram_x3f_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_untilTk_x3f_1456_ = l_Lean_Syntax_getArg(v___x_1451_, v___x_1232_);
v_untilProgram_x3f_1457_ = l_Lean_Syntax_getArg(v___x_1451_, v___x_1226_);
lean_dec(v___x_1451_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v_untilTk_x3f_1456_);
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v_untilProgram_x3f_1457_);
v___y_1420_ = v_args_x3f_1446_;
v___y_1421_ = v_rbTk_x3f_1447_;
v___y_1422_ = v_lbTk_x3f_1445_;
v___y_1423_ = v___x_1450_;
v_untilTk_x3f_1424_ = v___x_1458_;
v_untilProgram_x3f_1425_ = v___x_1459_;
v___y_1426_ = v___y_1448_;
v___y_1427_ = v___y_1449_;
goto v___jp_1419_;
}
}
else
{
lean_object* v___x_1460_; 
lean_dec(v___x_1451_);
v___x_1460_ = lean_box(0);
v___y_1420_ = v_args_x3f_1446_;
v___y_1421_ = v_rbTk_x3f_1447_;
v___y_1422_ = v_lbTk_x3f_1445_;
v___y_1423_ = v___x_1450_;
v_untilTk_x3f_1424_ = v___x_1460_;
v_untilProgram_x3f_1425_ = v___x_1460_;
v___y_1426_ = v___y_1448_;
v___y_1427_ = v___y_1449_;
goto v___jp_1419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindVCGen___boxed(lean_object* v_x_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Fmt_fmtGrindVCGen(v_x_1475_, v_a_1476_, v_a_1477_);
lean_dec_ref(v_a_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1(){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1485_ = l_Lean_Fmt_fmtAttribute;
v___x_1486_ = ((lean_object*)(l_Lean_Fmt_fmtGrindVCGen___closed__1));
v___x_1487_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___closed__1));
v___x_1488_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindVCGen___boxed), 3, 0);
v___x_1489_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1485_, v___x_1486_, v___x_1487_, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1___boxed(lean_object* v_a_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1();
return v_res_1491_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_WP_Tactic(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtSpecAttr___regBuiltin_Lean_Fmt_fmtSpecAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtInvariantAlts___regBuiltin_Lean_Fmt_fmtInvariantAlts__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeGrind___regBuiltin_Lean_Fmt_fmtVCGenDischargeGrind__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGenDischargeTactic___regBuiltin_Lean_Fmt_fmtVCGenDischargeTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtVCGen___regBuiltin_Lean_Fmt_fmtVCGen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_WP_Tactic_0__Lean_Fmt_fmtGrindVCGen___regBuiltin_Lean_Fmt_fmtGrindVCGen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_WP_Tactic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_WP_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_WP_Tactic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_WP_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_WP_Tactic(builtin);
}
#ifdef __cplusplus
}
#endif
