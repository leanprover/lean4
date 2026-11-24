// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Meta
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Meta import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Fmt_fmtRwLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSimpLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_tacticOptConfigItems___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEvalPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtEvalPrec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtEvalPrec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termEval_prec_"};
static const lean_object* l_Lean_Fmt_fmtEvalPrec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtEvalPrec___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtEvalPrec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(55, 225, 125, 23, 245, 187, 1, 255)}};
static const lean_object* l_Lean_Fmt_fmtEvalPrec___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEvalPrec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEvalPrec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtEvalPrec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 91, 226, 44, 149, 217, 170, 138)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEvalPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termEval_prio_"};
static const lean_object* l_Lean_Fmt_fmtEvalPrio___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEvalPrio___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtEvalPrio___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtEvalPrio___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEvalPrio___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtEvalPrio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 155, 229, 233, 248, 162, 206, 174)}};
static const lean_object* l_Lean_Fmt_fmtEvalPrio___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEvalPrio___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEvalPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEvalPrio___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtEvalPrio"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 76, 110, 55, 176, 174, 143, 253)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtErw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtErw___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtErw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtErw___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtErw___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tacticErw___"};
static const lean_object* l_Lean_Fmt_fmtErw___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtErw___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 238, 24, 88, 158, 88, 125, 211)}};
static const lean_object* l_Lean_Fmt_fmtErw___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtErw___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Fmt_fmtErw___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtErw___closed__4_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Fmt_fmtErw___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtErw___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l_Lean_Fmt_fmtErw___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__7_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__7_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__7_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtErw___closed__6_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l_Lean_Fmt_fmtErw___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtErw___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Fmt_fmtErw___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__9_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__9_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtErw___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtErw___closed__9_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtErw___closed__8_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Fmt_fmtErw___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtErw___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtErw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtErw___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fmtErw"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 126, 248, 121, 223, 57, 173, 151)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpAllKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpAllKind"};
static const lean_object* l_Lean_Fmt_fmtSimpAllKind___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpAllKind___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpAllKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 105, 142, 36, 223, 225, 123, 184)}};
static const lean_object* l_Lean_Fmt_fmtSimpAllKind___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpAllKind___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllKind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllKind___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtSimpAllKind"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 134, 255, 84, 243, 149, 58, 228)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDsimpKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpKind"};
static const lean_object* l_Lean_Fmt_fmtDsimpKind___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDsimpKind___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDsimpKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDsimpKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDsimpKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDsimpKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDsimpKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtDsimpKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDsimpKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDsimpKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 20, 82, 166, 5, 15, 155, 11)}};
static const lean_object* l_Lean_Fmt_fmtDsimpKind___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDsimpKind___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDsimpKind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDsimpKind___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtDsimpKind"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 100, 98, 144, 239, 82, 118, 4)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDeclareSimpLikeTactic_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDeclareSimpLikeTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "declareSimpLikeTactic"};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 29, 238, 199, 239, 152, 213, 112)}};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtDeclareSimpLikeTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 134, 221, 204, 214, 202, 57, 62)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simpAutoUnfold"};
static const lean_object* l_Lean_Fmt_fmtSimpAutoUnfold___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 205, 236, 180, 188, 29, 173, 240)}};
static const lean_object* l_Lean_Fmt_fmtSimpAutoUnfold___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "discharger"};
static const lean_object* l_Lean_Fmt_fmtSimpAutoUnfold___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAutoUnfold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 186, 255, 143, 150, 72, 152, 71)}};
static const lean_object* l_Lean_Fmt_fmtSimpAutoUnfold___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSimpAutoUnfold___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAutoUnfold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAutoUnfold___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtSimpAutoUnfold"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 229, 149, 59, 227, 155, 195, 183)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpArith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpArith"};
static const lean_object* l_Lean_Fmt_fmtSimpArith___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpArith___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpArith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpArith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpArith___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpArith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpArith___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpArith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpArith___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpArith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 47, 198, 44, 197, 94, 244, 200)}};
static const lean_object* l_Lean_Fmt_fmtSimpArith___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpArith___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpArith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpArith___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtSimpArith"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 122, 183, 165, 149, 58, 2, 204)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpArithBang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpArithBang"};
static const lean_object* l_Lean_Fmt_fmtSimpArithBang___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpArithBang___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpArithBang___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpArithBang___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpArithBang___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpArithBang___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpArithBang___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpArithBang___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpArithBang___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpArithBang___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 151, 237, 27, 117, 76, 215, 64)}};
static const lean_object* l_Lean_Fmt_fmtSimpArithBang___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpArithBang___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpArithBang(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpArithBang___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtSimpArithBang"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 123, 224, 135, 13, 148, 191, 255)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpAllAutoUnfold"};
static const lean_object* l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 140, 78, 27, 53, 62, 238, 147)}};
static const lean_object* l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllAutoUnfold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllAutoUnfold___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtSimpAllAutoUnfold"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 87, 50, 154, 121, 183, 22, 10)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpAllArith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpAllArith"};
static const lean_object* l_Lean_Fmt_fmtSimpAllArith___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpAllArith___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllArith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllArith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllArith___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllArith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllArith___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllArith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllArith___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpAllArith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 202, 96, 76, 254, 39, 20, 47)}};
static const lean_object* l_Lean_Fmt_fmtSimpAllArith___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpAllArith___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllArith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllArith___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtSimpAllArith"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 166, 164, 101, 15, 3, 43, 41)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpAllArithBang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simpAllArithBang"};
static const lean_object* l_Lean_Fmt_fmtSimpAllArithBang___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpAllArithBang___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllArithBang___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllArithBang___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllArithBang___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllArithBang___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllArithBang___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpAllArithBang___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpAllArithBang___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpAllArithBang___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 196, 181, 251, 41, 107, 56, 49)}};
static const lean_object* l_Lean_Fmt_fmtSimpAllArithBang___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpAllArithBang___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllArithBang(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllArithBang___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtSimpAllArithBang"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 69, 188, 78, 188, 96, 120, 85)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDSimpAutoUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dsimpAutoUnfold"};
static const lean_object* l_Lean_Fmt_fmtDSimpAutoUnfold___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDSimpAutoUnfold___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtErw___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDSimpAutoUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 242, 55, 207, 18, 232, 241, 249)}};
static const lean_object* l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimpAutoUnfold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimpAutoUnfold___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtDSimpAutoUnfold"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEvalPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 89, 252, 179, 40, 250, 131, 209)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEvalPrec(lean_object* v_x_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lean_Fmt_fmtEvalPrec___closed__2));
lean_inc(v_x_6_);
v___x_10_ = l_Lean_Syntax_isOfKind(v_x_6_, v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; 
lean_dec(v_x_6_);
v___x_11_ = l_Lean_Fmt_Error_partialFormatter;
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v_a_8_);
return v___x_12_;
}
else
{
lean_object* v___x_13_; lean_object* v_evalPrecTk_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v_evalPrecTk_14_ = l_Lean_Syntax_getArg(v_x_6_, v___x_13_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = l_Lean_Syntax_getArg(v_x_6_, v___x_15_);
lean_dec(v_x_6_);
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
v___x_19_ = lean_array_push(v___x_18_, v_evalPrecTk_14_);
v___x_20_ = lean_array_push(v___x_19_, v___x_16_);
v___x_21_ = l_Lean_Fmt_fmtAppLike(v___x_20_, v_a_7_, v_a_8_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEvalPrec___boxed(lean_object* v_x_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Fmt_fmtEvalPrec(v_x_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_a_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1(){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_33_ = l_Lean_Fmt_fmtAttribute;
v___x_34_ = ((lean_object*)(l_Lean_Fmt_fmtEvalPrec___closed__2));
v___x_35_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___closed__2));
v___x_36_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEvalPrec___boxed), 3, 0);
v___x_37_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_33_, v___x_34_, v___x_35_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1___boxed(lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1();
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEvalPrio(lean_object* v_x_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = ((lean_object*)(l_Lean_Fmt_fmtEvalPrio___closed__1));
lean_inc(v_x_44_);
v___x_48_ = l_Lean_Syntax_isOfKind(v_x_44_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_x_44_);
v___x_49_ = l_Lean_Fmt_Error_partialFormatter;
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v_a_46_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v_evalPrioTk_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_51_ = lean_unsigned_to_nat(0u);
v_evalPrioTk_52_ = l_Lean_Syntax_getArg(v_x_44_, v___x_51_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = l_Lean_Syntax_getArg(v_x_44_, v___x_53_);
lean_dec(v_x_44_);
v___x_55_ = lean_unsigned_to_nat(2u);
v___x_56_ = lean_mk_empty_array_with_capacity(v___x_55_);
v___x_57_ = lean_array_push(v___x_56_, v_evalPrioTk_52_);
v___x_58_ = lean_array_push(v___x_57_, v___x_54_);
v___x_59_ = l_Lean_Fmt_fmtAppLike(v___x_58_, v_a_45_, v_a_46_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEvalPrio___boxed(lean_object* v_x_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Fmt_fmtEvalPrio(v_x_60_, v_a_61_, v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1(){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_70_ = l_Lean_Fmt_fmtAttribute;
v___x_71_ = ((lean_object*)(l_Lean_Fmt_fmtEvalPrio___closed__1));
v___x_72_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___closed__1));
v___x_73_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEvalPrio___boxed), 3, 0);
v___x_74_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_70_, v___x_71_, v___x_72_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1___boxed(lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtErw(lean_object* v_x_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__3));
lean_inc(v_x_103_);
v___x_107_ = l_Lean_Syntax_isOfKind(v_x_103_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_x_103_);
v___x_108_ = l_Lean_Fmt_Error_partialFormatter;
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_a_105_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v_cfg_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v_cfg_111_ = l_Lean_Syntax_getArg(v_x_103_, v___x_110_);
v___x_112_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_111_);
v___x_113_ = l_Lean_Syntax_isOfKind(v_cfg_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_cfg_111_);
lean_dec(v_x_103_);
v___x_114_ = l_Lean_Fmt_Error_partialFormatter;
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_a_105_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_103_, v___x_116_);
v___x_118_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__7));
lean_inc(v___x_117_);
v___x_119_ = l_Lean_Syntax_isOfKind(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v___x_117_);
lean_dec(v_cfg_111_);
lean_dec(v_x_103_);
v___x_120_ = l_Lean_Fmt_Error_partialFormatter;
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_a_105_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v_erwTk_123_; lean_object* v_loc_x3f_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v_erwTk_123_ = l_Lean_Syntax_getArg(v_x_103_, v___x_122_);
v___x_130_ = lean_unsigned_to_nat(3u);
v___x_131_ = l_Lean_Syntax_getArg(v_x_103_, v___x_130_);
lean_dec(v_x_103_);
v___x_132_ = l_Lean_Syntax_isNone(v___x_131_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
lean_inc(v___x_131_);
v___x_133_ = l_Lean_Syntax_matchesNull(v___x_131_, v___x_110_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v___x_131_);
lean_dec(v_erwTk_123_);
lean_dec(v___x_117_);
lean_dec(v_cfg_111_);
v___x_134_ = l_Lean_Fmt_Error_partialFormatter;
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_105_);
return v___x_135_;
}
else
{
lean_object* v_loc_x3f_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_loc_x3f_136_ = l_Lean_Syntax_getArg(v___x_131_, v___x_122_);
lean_dec(v___x_131_);
v___x_137_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__9));
lean_inc(v_loc_x3f_136_);
v___x_138_ = l_Lean_Syntax_isOfKind(v_loc_x3f_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_loc_x3f_136_);
lean_dec(v_erwTk_123_);
lean_dec(v___x_117_);
lean_dec(v_cfg_111_);
v___x_139_ = l_Lean_Fmt_Error_partialFormatter;
v___x_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_a_105_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v_loc_x3f_136_);
v_loc_x3f_125_ = v___x_141_;
v___y_126_ = v_a_104_;
v___y_127_ = v_a_105_;
goto v___jp_124_;
}
}
}
else
{
lean_object* v___x_142_; 
lean_dec(v___x_131_);
v___x_142_ = lean_box(0);
v_loc_x3f_125_ = v___x_142_;
v___y_126_ = v_a_104_;
v___y_127_ = v_a_105_;
goto v___jp_124_;
}
v___jp_124_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v_cfg_111_);
v___x_129_ = l_Lean_Fmt_fmtRwLike(v_erwTk_123_, v___x_128_, v___x_117_, v_loc_x3f_125_, v___y_126_, v___y_127_);
return v___x_129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtErw___boxed(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Fmt_fmtErw(v_x_143_, v_a_144_, v_a_145_);
lean_dec_ref(v_a_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1(){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = l_Lean_Fmt_fmtAttribute;
v___x_154_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__3));
v___x_155_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___closed__1));
v___x_156_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtErw___boxed), 3, 0);
v___x_157_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_153_, v___x_154_, v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1___boxed(lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1();
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllKind(lean_object* v_x_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAllKind___closed__1));
lean_inc(v_x_166_);
v___x_170_ = l_Lean_Syntax_isOfKind(v_x_166_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_x_166_);
v___x_171_ = l_Lean_Fmt_Error_partialFormatter;
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_a_168_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v_lbTk_174_; lean_object* v___x_175_; lean_object* v_allTk_176_; lean_object* v___x_177_; lean_object* v_colonEqTk_178_; lean_object* v___x_179_; lean_object* v_trueTk_180_; lean_object* v___x_181_; lean_object* v_rbTk_182_; lean_object* v___x_183_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v_lbTk_174_ = l_Lean_Syntax_getArg(v_x_166_, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(1u);
v_allTk_176_ = l_Lean_Syntax_getArg(v_x_166_, v___x_175_);
v___x_177_ = lean_unsigned_to_nat(2u);
v_colonEqTk_178_ = l_Lean_Syntax_getArg(v_x_166_, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(3u);
v_trueTk_180_ = l_Lean_Syntax_getArg(v_x_166_, v___x_179_);
v___x_181_ = lean_unsigned_to_nat(4u);
v_rbTk_182_ = l_Lean_Syntax_getArg(v_x_166_, v___x_181_);
lean_dec(v_x_166_);
v___x_183_ = l_Lean_Fmt_fmtNamedArgumentTerm(v_lbTk_174_, v_allTk_176_, v_colonEqTk_178_, v_trueTk_180_, v_rbTk_182_, v_a_167_, v_a_168_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllKind___boxed(lean_object* v_x_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Fmt_fmtSimpAllKind(v_x_184_, v_a_185_, v_a_186_);
lean_dec_ref(v_a_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1(){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = l_Lean_Fmt_fmtAttribute;
v___x_195_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAllKind___closed__1));
v___x_196_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___closed__1));
v___x_197_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpAllKind___boxed), 3, 0);
v___x_198_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_194_, v___x_195_, v___x_196_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1___boxed(lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1();
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDsimpKind(lean_object* v_x_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Fmt_fmtDsimpKind___closed__1));
lean_inc(v_x_207_);
v___x_211_ = l_Lean_Syntax_isOfKind(v_x_207_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_x_207_);
v___x_212_ = l_Lean_Fmt_Error_partialFormatter;
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_209_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v_lbTk_215_; lean_object* v___x_216_; lean_object* v_dsimpTk_217_; lean_object* v___x_218_; lean_object* v_colonEqTk_219_; lean_object* v___x_220_; lean_object* v_trueTk_221_; lean_object* v___x_222_; lean_object* v_rbTk_223_; lean_object* v___x_224_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v_lbTk_215_ = l_Lean_Syntax_getArg(v_x_207_, v___x_214_);
v___x_216_ = lean_unsigned_to_nat(1u);
v_dsimpTk_217_ = l_Lean_Syntax_getArg(v_x_207_, v___x_216_);
v___x_218_ = lean_unsigned_to_nat(2u);
v_colonEqTk_219_ = l_Lean_Syntax_getArg(v_x_207_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(3u);
v_trueTk_221_ = l_Lean_Syntax_getArg(v_x_207_, v___x_220_);
v___x_222_ = lean_unsigned_to_nat(4u);
v_rbTk_223_ = l_Lean_Syntax_getArg(v_x_207_, v___x_222_);
lean_dec(v_x_207_);
v___x_224_ = l_Lean_Fmt_fmtNamedArgumentTerm(v_lbTk_215_, v_dsimpTk_217_, v_colonEqTk_219_, v_trueTk_221_, v_rbTk_223_, v_a_208_, v_a_209_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDsimpKind___boxed(lean_object* v_x_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Fmt_fmtDsimpKind(v_x_225_, v_a_226_, v_a_227_);
lean_dec_ref(v_a_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1(){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_235_ = l_Lean_Fmt_fmtAttribute;
v___x_236_ = ((lean_object*)(l_Lean_Fmt_fmtDsimpKind___closed__1));
v___x_237_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___closed__1));
v___x_238_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDsimpKind___boxed), 3, 0);
v___x_239_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_235_, v___x_236_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1___boxed(lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1();
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDeclareSimpLikeTactic_spec__0(size_t v_sz_242_, size_t v_i_243_, lean_object* v_bs_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_lt(v_i_243_, v_sz_242_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_bs_244_);
lean_ctor_set(v___x_248_, 1, v___y_246_);
return v___x_248_;
}
else
{
lean_object* v_v_249_; lean_object* v___x_250_; 
v_v_249_ = lean_array_uget_borrowed(v_bs_244_, v_i_243_);
lean_inc(v_v_249_);
v___x_250_ = l_Lean_Fmt_fmt(v_v_249_, v___y_245_, v___y_246_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v_a_252_; lean_object* v___x_253_; lean_object* v_bs_x27_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
v_a_252_ = lean_ctor_get(v___x_250_, 1);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_250_, 2);
v___x_253_ = lean_unsigned_to_nat(0u);
v_bs_x27_254_ = lean_array_uset(v_bs_244_, v_i_243_, v___x_253_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_add(v_i_243_, v___x_255_);
v___x_257_ = lean_array_uset(v_bs_x27_254_, v_i_243_, v_a_251_);
v_i_243_ = v___x_256_;
v_bs_244_ = v___x_257_;
v___y_246_ = v_a_252_;
goto _start;
}
else
{
lean_object* v_a_259_; lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_bs_244_);
v_a_259_ = lean_ctor_get(v___x_250_, 0);
v_a_260_ = lean_ctor_get(v___x_250_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_250_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_inc(v_a_259_);
lean_dec(v___x_250_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_259_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDeclareSimpLikeTactic_spec__0___boxed(lean_object* v_sz_268_, lean_object* v_i_269_, lean_object* v_bs_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
size_t v_sz_boxed_273_; size_t v_i_boxed_274_; lean_object* v_res_275_; 
v_sz_boxed_273_ = lean_unbox_usize(v_sz_268_);
lean_dec(v_sz_268_);
v_i_boxed_274_ = lean_unbox_usize(v_i_269_);
lean_dec(v_i_269_);
v_res_275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDeclareSimpLikeTactic_spec__0(v_sz_boxed_273_, v_i_boxed_274_, v_bs_270_, v___y_271_, v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic(lean_object* v_x_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v_opt_x3f_401_; lean_object* v___y_402_; lean_object* v___y_403_; 
v___x_301_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1));
lean_inc(v_x_298_);
v___x_302_ = l_Lean_Syntax_isOfKind(v_x_298_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_x_298_);
v___x_447_ = l_Lean_Fmt_Error_partialFormatter;
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_a_300_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; lean_object* v_doc_x3f_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_465_ = l_Lean_Syntax_getArg(v_x_298_, v___x_449_);
v___x_466_ = l_Lean_Syntax_isNone(v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_465_);
v___x_468_ = l_Lean_Syntax_matchesNull(v___x_465_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v___x_465_);
lean_dec(v_x_298_);
v___x_469_ = l_Lean_Fmt_Error_partialFormatter;
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v_a_300_);
return v___x_470_;
}
else
{
lean_object* v_doc_x3f_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_doc_x3f_471_ = l_Lean_Syntax_getArg(v___x_465_, v___x_449_);
lean_dec(v___x_465_);
v___x_472_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__10));
lean_inc(v_doc_x3f_471_);
v___x_473_ = l_Lean_Syntax_isOfKind(v_doc_x3f_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v_doc_x3f_471_);
lean_dec(v_x_298_);
v___x_474_ = l_Lean_Fmt_Error_partialFormatter;
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v_a_300_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v_doc_x3f_471_);
v_doc_x3f_451_ = v___x_476_;
v___y_452_ = v_a_299_;
v___y_453_ = v_a_300_;
goto v___jp_450_;
}
}
}
else
{
lean_object* v___x_477_; 
lean_dec(v___x_465_);
v___x_477_ = lean_box(0);
v_doc_x3f_451_ = v___x_477_;
v___y_452_ = v_a_299_;
v___y_453_ = v_a_300_;
goto v___jp_450_;
}
v___jp_450_:
{
lean_object* v___x_454_; lean_object* v_declTk_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v_declTk_455_ = l_Lean_Syntax_getArg(v_x_298_, v___x_454_);
v___x_456_ = lean_unsigned_to_nat(2u);
v___x_457_ = l_Lean_Syntax_getArg(v_x_298_, v___x_456_);
v___x_458_ = l_Lean_Syntax_isNone(v___x_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
lean_inc(v___x_457_);
v___x_459_ = l_Lean_Syntax_matchesNull(v___x_457_, v___x_454_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v___x_457_);
lean_dec(v_declTk_455_);
lean_dec(v_doc_x3f_451_);
lean_dec(v_x_298_);
v___x_460_ = l_Lean_Fmt_Error_partialFormatter;
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___y_453_);
return v___x_461_;
}
else
{
lean_object* v_opt_x3f_462_; lean_object* v___x_463_; 
v_opt_x3f_462_ = l_Lean_Syntax_getArg(v___x_457_, v___x_449_);
lean_dec(v___x_457_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_opt_x3f_462_);
v___y_399_ = v_doc_x3f_451_;
v___y_400_ = v_declTk_455_;
v_opt_x3f_401_ = v___x_463_;
v___y_402_ = v___y_452_;
v___y_403_ = v___y_453_;
goto v___jp_398_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v___x_457_);
v___x_464_ = lean_box(0);
v___y_399_ = v_doc_x3f_451_;
v___y_400_ = v_declTk_455_;
v_opt_x3f_401_ = v___x_464_;
v___y_402_ = v___y_452_;
v___y_403_ = v___y_453_;
goto v___jp_398_;
}
}
}
v___jp_303_:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Fmt_fmt_x3f(v___y_312_, v___y_304_, v___y_307_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v_a_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
v_a_315_ = lean_ctor_get(v___x_313_, 1);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_313_, 2);
v___x_316_ = 0;
v___x_317_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_317_, 0, v___x_302_);
lean_ctor_set_uint8(v___x_317_, 1, v___x_316_);
lean_ctor_set_uint8(v___x_317_, 2, v___x_316_);
lean_ctor_set_uint8(v___x_317_, 3, v___x_316_);
v___x_318_ = l_Lean_Fmt_fmt(v___y_311_, v___y_304_, v_a_315_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v_a_320_; lean_object* v___x_321_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
v_a_320_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_318_, 2);
v___x_321_ = l_Lean_Fmt_fmt(v___y_305_, v___y_304_, v_a_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
v_a_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_321_, 2);
v___x_324_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v___y_310_, v_a_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v_a_326_; size_t v_sz_327_; size_t v___x_328_; lean_object* v___x_329_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
v_a_326_ = lean_ctor_get(v___x_324_, 1);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_324_, 2);
v_sz_327_ = lean_array_size(v_a_325_);
v___x_328_ = ((size_t)0ULL);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDeclareSimpLikeTactic_spec__0(v_sz_327_, v___x_328_, v_a_325_, v___y_304_, v_a_326_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_352_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_a_331_ = lean_ctor_get(v___x_329_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_352_ == 0)
{
v___x_333_ = v___x_329_;
v_isShared_334_ = v_isSharedCheck_352_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_352_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_335_ = lean_unsigned_to_nat(2u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
lean_inc_ref(v___x_336_);
v___x_337_ = lean_array_push(v___x_336_, v___y_309_);
v___x_338_ = lean_array_push(v___x_337_, v_a_314_);
lean_inc_ref(v___x_317_);
v___x_339_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_338_, v___x_317_);
v___x_340_ = lean_mk_empty_array_with_capacity(v___y_308_);
v___x_341_ = lean_array_push(v___x_340_, v___x_339_);
v___x_342_ = lean_array_push(v___x_341_, v_a_319_);
v___x_343_ = lean_array_push(v___x_342_, v_a_322_);
v___x_344_ = l_Array_append___redArg(v___x_343_, v_a_330_);
lean_dec(v_a_330_);
v___x_345_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_344_, v___x_317_);
v___x_346_ = lean_array_push(v___x_336_, v___y_306_);
v___x_347_ = lean_array_push(v___x_346_, v___x_345_);
v___x_348_ = l_Lean_Fmt_Layouts_lines(v___x_347_);
lean_dec_ref(v___x_347_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_348_);
v___x_350_ = v___x_333_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_a_331_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_a_322_);
lean_dec(v_a_319_);
lean_dec_ref_known(v___x_317_, 0);
lean_dec(v_a_314_);
lean_dec_ref(v___y_309_);
lean_dec_ref(v___y_306_);
v_a_353_ = lean_ctor_get(v___x_329_, 0);
v_a_354_ = lean_ctor_get(v___x_329_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_329_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_dec(v___x_329_);
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
lean_object* v_a_362_; lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_a_322_);
lean_dec(v_a_319_);
lean_dec_ref_known(v___x_317_, 0);
lean_dec(v_a_314_);
lean_dec_ref(v___y_309_);
lean_dec_ref(v___y_306_);
v_a_362_ = lean_ctor_get(v___x_324_, 0);
v_a_363_ = lean_ctor_get(v___x_324_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_324_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_inc(v_a_362_);
lean_dec(v___x_324_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_362_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_dec(v_a_319_);
lean_dec_ref_known(v___x_317_, 0);
lean_dec(v_a_314_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec_ref(v___y_306_);
return v___x_321_;
}
}
else
{
lean_dec_ref_known(v___x_317_, 0);
lean_dec(v_a_314_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
return v___x_318_;
}
}
else
{
lean_dec(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
return v___x_313_;
}
}
v___jp_371_:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Fmt_fmt_x3f(v___y_380_, v___y_372_, v___y_378_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
v_a_383_ = lean_ctor_get(v___x_381_, 1);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_381_, 2);
v___x_384_ = l_Lean_Fmt_fmt(v___y_377_, v___y_372_, v_a_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
if (lean_obj_tag(v___y_373_) == 0)
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
v_a_386_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_384_, 2);
v___x_387_ = lean_box(0);
v___y_304_ = v___y_372_;
v___y_305_ = v___y_374_;
v___y_306_ = v_a_382_;
v___y_307_ = v_a_386_;
v___y_308_ = v___y_376_;
v___y_309_ = v_a_385_;
v___y_310_ = v___y_375_;
v___y_311_ = v___y_379_;
v___y_312_ = v___x_387_;
goto v___jp_303_;
}
else
{
lean_object* v_a_388_; lean_object* v_a_389_; lean_object* v_val_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_a_388_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_388_);
v_a_389_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_384_, 2);
v_val_390_ = lean_ctor_get(v___y_373_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___y_373_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___y_373_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_val_390_);
lean_dec(v___y_373_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_val_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
v___y_304_ = v___y_372_;
v___y_305_ = v___y_374_;
v___y_306_ = v_a_382_;
v___y_307_ = v_a_389_;
v___y_308_ = v___y_376_;
v___y_309_ = v_a_388_;
v___y_310_ = v___y_375_;
v___y_311_ = v___y_379_;
v___y_312_ = v___x_395_;
goto v___jp_303_;
}
}
}
}
else
{
lean_dec(v_a_382_);
lean_dec(v___y_379_);
lean_dec(v___y_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
return v___x_384_;
}
}
else
{
lean_dec(v___y_379_);
lean_dec(v___y_377_);
lean_dec(v___y_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
return v___x_381_;
}
}
v___jp_398_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_404_ = lean_unsigned_to_nat(3u);
v___x_405_ = l_Lean_Syntax_getArg(v_x_298_, v___x_404_);
v___x_406_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__3));
v___x_407_ = l_Lean_Syntax_isOfKind(v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_opt_x3f_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v_x_298_);
v___x_408_ = l_Lean_Fmt_Error_partialFormatter;
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___y_403_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_410_ = lean_unsigned_to_nat(4u);
v___x_411_ = l_Lean_Syntax_getArg(v_x_298_, v___x_410_);
v___x_412_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__5));
lean_inc(v___x_411_);
v___x_413_ = l_Lean_Syntax_isOfKind(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v___x_411_);
lean_dec(v_opt_x3f_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v_x_298_);
v___x_414_ = l_Lean_Fmt_Error_partialFormatter;
v___x_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___y_403_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_unsigned_to_nat(5u);
v___x_417_ = l_Lean_Syntax_getArg(v_x_298_, v___x_416_);
v___x_418_ = l_Lean_Syntax_isOfKind(v___x_417_, v___x_406_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v___x_411_);
lean_dec(v_opt_x3f_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v_x_298_);
v___x_419_ = l_Lean_Fmt_Error_partialFormatter;
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___y_403_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_421_ = lean_unsigned_to_nat(6u);
v___x_422_ = l_Lean_Syntax_getArg(v_x_298_, v___x_421_);
v___x_423_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__7));
lean_inc(v___x_422_);
v___x_424_ = l_Lean_Syntax_isOfKind(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v___x_422_);
lean_dec(v___x_411_);
lean_dec(v_opt_x3f_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v_x_298_);
v___x_425_ = l_Lean_Fmt_Error_partialFormatter;
v___x_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___y_403_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_427_ = lean_unsigned_to_nat(7u);
v___x_428_ = l_Lean_Syntax_getArg(v_x_298_, v___x_427_);
v___x_429_ = l_Lean_Syntax_isOfKind(v___x_428_, v___x_406_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v___x_422_);
lean_dec(v___x_411_);
lean_dec(v_opt_x3f_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v_x_298_);
v___x_430_ = l_Lean_Fmt_Error_partialFormatter;
v___x_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___y_403_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v_cfg_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_432_ = lean_unsigned_to_nat(8u);
v_cfg_433_ = l_Lean_Syntax_getArg(v_x_298_, v___x_432_);
lean_dec(v_x_298_);
v___x_434_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_433_);
v___x_435_ = l_Lean_Syntax_isOfKind(v_cfg_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec(v_cfg_433_);
lean_dec(v___x_422_);
lean_dec(v___x_411_);
lean_dec(v_opt_x3f_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
v___x_436_ = l_Lean_Fmt_Error_partialFormatter;
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___y_403_);
return v___x_437_;
}
else
{
if (lean_obj_tag(v___y_399_) == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_box(0);
v___y_372_ = v___y_402_;
v___y_373_ = v_opt_x3f_401_;
v___y_374_ = v___x_422_;
v___y_375_ = v_cfg_433_;
v___y_376_ = v___x_404_;
v___y_377_ = v___y_400_;
v___y_378_ = v___y_403_;
v___y_379_ = v___x_411_;
v___y_380_ = v___x_438_;
goto v___jp_371_;
}
else
{
lean_object* v_val_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_val_439_ = lean_ctor_get(v___y_399_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___y_399_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___y_399_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_val_439_);
lean_dec(v___y_399_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_val_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
v___y_372_ = v___y_402_;
v___y_373_ = v_opt_x3f_401_;
v___y_374_ = v___x_422_;
v___y_375_ = v_cfg_433_;
v___y_376_ = v___x_404_;
v___y_377_ = v___y_400_;
v___y_378_ = v___y_403_;
v___y_379_ = v___x_411_;
v___y_380_ = v___x_444_;
goto v___jp_371_;
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
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareSimpLikeTactic___boxed(lean_object* v_x_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Fmt_fmtDeclareSimpLikeTactic(v_x_478_, v_a_479_, v_a_480_);
lean_dec_ref(v_a_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1(){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_488_ = l_Lean_Fmt_fmtAttribute;
v___x_489_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareSimpLikeTactic___closed__1));
v___x_490_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___closed__1));
v___x_491_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeclareSimpLikeTactic___boxed), 3, 0);
v___x_492_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_488_, v___x_489_, v___x_490_, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1___boxed(lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1();
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAutoUnfold(lean_object* v_x_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__1));
lean_inc(v_x_507_);
v___x_511_ = l_Lean_Syntax_isOfKind(v_x_507_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_x_507_);
v___x_512_ = l_Lean_Fmt_Error_partialFormatter;
v___x_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v_a_509_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v_cfg_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v_cfg_515_ = l_Lean_Syntax_getArg(v_x_507_, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_515_);
v___x_517_ = l_Lean_Syntax_isOfKind(v_cfg_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_cfg_515_);
lean_dec(v_x_507_);
v___x_518_ = l_Lean_Fmt_Error_partialFormatter;
v___x_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v_a_509_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v_tk_521_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v_loc_x3f_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v_lbTk_x3f_547_; lean_object* v_args_x3f_548_; lean_object* v_rbTk_x3f_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___x_565_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v_only_x3f_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v_disch_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v_tk_521_ = l_Lean_Syntax_getArg(v_x_507_, v___x_520_);
v___x_565_ = lean_unsigned_to_nat(2u);
v___x_599_ = l_Lean_Syntax_getArg(v_x_507_, v___x_565_);
v___x_600_ = l_Lean_Syntax_isNone(v___x_599_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
lean_inc(v___x_599_);
v___x_601_ = l_Lean_Syntax_matchesNull(v___x_599_, v___x_514_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v___x_599_);
lean_dec(v_tk_521_);
lean_dec(v_cfg_515_);
lean_dec(v_x_507_);
v___x_602_ = l_Lean_Fmt_Error_partialFormatter;
v___x_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v_a_509_);
return v___x_603_;
}
else
{
lean_object* v_disch_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_disch_604_ = l_Lean_Syntax_getArg(v___x_599_, v___x_520_);
lean_dec(v___x_599_);
v___x_605_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__3));
lean_inc(v_disch_604_);
v___x_606_ = l_Lean_Syntax_isOfKind(v_disch_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_disch_604_);
lean_dec(v_tk_521_);
lean_dec(v_cfg_515_);
lean_dec(v_x_507_);
v___x_607_ = l_Lean_Fmt_Error_partialFormatter;
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_a_509_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v_disch_604_);
v_disch_587_ = v___x_609_;
v___y_588_ = v_a_508_;
v___y_589_ = v_a_509_;
goto v___jp_586_;
}
}
}
else
{
lean_object* v___x_610_; 
lean_dec(v___x_599_);
v___x_610_ = lean_box(0);
v_disch_587_ = v___x_610_;
v___y_588_ = v_a_508_;
v___y_589_ = v_a_509_;
goto v___jp_586_;
}
v___jp_522_:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_514_);
v___x_532_ = lean_array_push(v___x_531_, v_tk_521_);
if (lean_obj_tag(v___y_524_) == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_box(0);
v___x_534_ = l_Lean_Fmt_fmtSimpLike(v___x_532_, v_cfg_515_, v___y_525_, v___y_526_, v___y_527_, v___x_533_, v___y_523_, v_loc_x3f_528_, v___y_529_, v___y_530_);
return v___x_534_;
}
else
{
lean_object* v_val_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_543_; 
v_val_535_ = lean_ctor_get(v___y_524_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___y_524_);
if (v_isSharedCheck_543_ == 0)
{
v___x_537_ = v___y_524_;
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_val_535_);
lean_dec(v___y_524_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_val_535_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Fmt_fmtSimpLike(v___x_532_, v_cfg_515_, v___y_525_, v___y_526_, v___y_527_, v___x_540_, v___y_523_, v_loc_x3f_528_, v___y_529_, v___y_530_);
return v___x_541_;
}
}
}
}
v___jp_544_:
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_unsigned_to_nat(5u);
v___x_553_ = l_Lean_Syntax_getArg(v_x_507_, v___x_552_);
lean_dec(v_x_507_);
v___x_554_ = l_Lean_Syntax_isNone(v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; 
lean_inc(v___x_553_);
v___x_555_ = l_Lean_Syntax_matchesNull(v___x_553_, v___x_514_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v___x_553_);
lean_dec(v_rbTk_x3f_549_);
lean_dec(v_args_x3f_548_);
lean_dec(v_lbTk_x3f_547_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
lean_dec(v_tk_521_);
lean_dec(v_cfg_515_);
v___x_556_ = l_Lean_Fmt_Error_partialFormatter;
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___y_551_);
return v___x_557_;
}
else
{
lean_object* v_loc_x3f_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_loc_x3f_558_ = l_Lean_Syntax_getArg(v___x_553_, v___x_520_);
lean_dec(v___x_553_);
v___x_559_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__9));
lean_inc(v_loc_x3f_558_);
v___x_560_ = l_Lean_Syntax_isOfKind(v_loc_x3f_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_loc_x3f_558_);
lean_dec(v_rbTk_x3f_549_);
lean_dec(v_args_x3f_548_);
lean_dec(v_lbTk_x3f_547_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
lean_dec(v_tk_521_);
lean_dec(v_cfg_515_);
v___x_561_ = l_Lean_Fmt_Error_partialFormatter;
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___y_551_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v_loc_x3f_558_);
v___y_523_ = v_rbTk_x3f_549_;
v___y_524_ = v_args_x3f_548_;
v___y_525_ = v___y_545_;
v___y_526_ = v___y_546_;
v___y_527_ = v_lbTk_x3f_547_;
v_loc_x3f_528_ = v___x_563_;
v___y_529_ = v___y_550_;
v___y_530_ = v___y_551_;
goto v___jp_522_;
}
}
}
else
{
lean_object* v___x_564_; 
lean_dec(v___x_553_);
v___x_564_ = lean_box(0);
v___y_523_ = v_rbTk_x3f_549_;
v___y_524_ = v_args_x3f_548_;
v___y_525_ = v___y_545_;
v___y_526_ = v___y_546_;
v___y_527_ = v_lbTk_x3f_547_;
v_loc_x3f_528_ = v___x_564_;
v___y_529_ = v___y_550_;
v___y_530_ = v___y_551_;
goto v___jp_522_;
}
}
v___jp_566_:
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(4u);
v___x_573_ = l_Lean_Syntax_getArg(v_x_507_, v___x_572_);
v___x_574_ = l_Lean_Syntax_isNone(v___x_573_);
if (v___x_574_ == 0)
{
uint8_t v___x_575_; 
lean_inc(v___x_573_);
v___x_575_ = l_Lean_Syntax_matchesNull(v___x_573_, v___y_568_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___x_573_);
lean_dec(v_only_x3f_569_);
lean_dec(v___y_567_);
lean_dec(v_tk_521_);
lean_dec(v_cfg_515_);
lean_dec(v_x_507_);
v___x_576_ = l_Lean_Fmt_Error_partialFormatter;
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___y_571_);
return v___x_577_;
}
else
{
lean_object* v_lbTk_x3f_578_; lean_object* v___x_579_; lean_object* v_rbTk_x3f_580_; lean_object* v_args_x3f_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_lbTk_x3f_578_ = l_Lean_Syntax_getArg(v___x_573_, v___x_520_);
v___x_579_ = l_Lean_Syntax_getArg(v___x_573_, v___x_514_);
v_rbTk_x3f_580_ = l_Lean_Syntax_getArg(v___x_573_, v___x_565_);
lean_dec(v___x_573_);
v_args_x3f_581_ = l_Lean_Syntax_getArgs(v___x_579_);
lean_dec(v___x_579_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_lbTk_x3f_578_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v_args_x3f_581_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_rbTk_x3f_580_);
v___y_545_ = v___y_567_;
v___y_546_ = v_only_x3f_569_;
v_lbTk_x3f_547_ = v___x_582_;
v_args_x3f_548_ = v___x_583_;
v_rbTk_x3f_549_ = v___x_584_;
v___y_550_ = v___y_570_;
v___y_551_ = v___y_571_;
goto v___jp_544_;
}
}
else
{
lean_object* v___x_585_; 
lean_dec(v___x_573_);
v___x_585_ = lean_box(0);
v___y_545_ = v___y_567_;
v___y_546_ = v_only_x3f_569_;
v_lbTk_x3f_547_ = v___x_585_;
v_args_x3f_548_ = v___x_585_;
v_rbTk_x3f_549_ = v___x_585_;
v___y_550_ = v___y_570_;
v___y_551_ = v___y_571_;
goto v___jp_544_;
}
}
v___jp_586_:
{
lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(3u);
v___x_591_ = l_Lean_Syntax_getArg(v_x_507_, v___x_590_);
v___x_592_ = l_Lean_Syntax_isNone(v___x_591_);
if (v___x_592_ == 0)
{
uint8_t v___x_593_; 
lean_inc(v___x_591_);
v___x_593_ = l_Lean_Syntax_matchesNull(v___x_591_, v___x_514_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v___x_591_);
lean_dec(v_disch_587_);
lean_dec(v_tk_521_);
lean_dec(v_cfg_515_);
lean_dec(v_x_507_);
v___x_594_ = l_Lean_Fmt_Error_partialFormatter;
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___y_589_);
return v___x_595_;
}
else
{
lean_object* v_only_x3f_596_; lean_object* v___x_597_; 
v_only_x3f_596_ = l_Lean_Syntax_getArg(v___x_591_, v___x_520_);
lean_dec(v___x_591_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_only_x3f_596_);
v___y_567_ = v_disch_587_;
v___y_568_ = v___x_590_;
v_only_x3f_569_ = v___x_597_;
v___y_570_ = v___y_588_;
v___y_571_ = v___y_589_;
goto v___jp_566_;
}
}
else
{
lean_object* v___x_598_; 
lean_dec(v___x_591_);
v___x_598_ = lean_box(0);
v___y_567_ = v_disch_587_;
v___y_568_ = v___x_590_;
v_only_x3f_569_ = v___x_598_;
v___y_570_ = v___y_588_;
v___y_571_ = v___y_589_;
goto v___jp_566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAutoUnfold___boxed(lean_object* v_x_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Fmt_fmtSimpAutoUnfold(v_x_611_, v_a_612_, v_a_613_);
lean_dec_ref(v_a_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1(){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_621_ = l_Lean_Fmt_fmtAttribute;
v___x_622_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__1));
v___x_623_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___closed__1));
v___x_624_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpAutoUnfold___boxed), 3, 0);
v___x_625_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_621_, v___x_622_, v___x_623_, v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1___boxed(lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1();
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpArith(lean_object* v_x_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_Fmt_fmtSimpArith___closed__1));
lean_inc(v_x_634_);
v___x_638_ = l_Lean_Syntax_isOfKind(v_x_634_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v_x_634_);
v___x_639_ = l_Lean_Fmt_Error_partialFormatter;
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_a_636_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v_cfg_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v_cfg_642_ = l_Lean_Syntax_getArg(v_x_634_, v___x_641_);
v___x_643_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_642_);
v___x_644_ = l_Lean_Syntax_isOfKind(v_cfg_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_cfg_642_);
lean_dec(v_x_634_);
v___x_645_ = l_Lean_Fmt_Error_partialFormatter;
v___x_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v_a_636_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v_tk_648_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v_loc_x3f_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v_lbTk_x3f_674_; lean_object* v_args_x3f_675_; lean_object* v_rbTk_x3f_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___x_692_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v_only_x3f_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v_disch_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v_tk_648_ = l_Lean_Syntax_getArg(v_x_634_, v___x_647_);
v___x_692_ = lean_unsigned_to_nat(2u);
v___x_726_ = l_Lean_Syntax_getArg(v_x_634_, v___x_692_);
v___x_727_ = l_Lean_Syntax_isNone(v___x_726_);
if (v___x_727_ == 0)
{
uint8_t v___x_728_; 
lean_inc(v___x_726_);
v___x_728_ = l_Lean_Syntax_matchesNull(v___x_726_, v___x_641_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v___x_726_);
lean_dec(v_tk_648_);
lean_dec(v_cfg_642_);
lean_dec(v_x_634_);
v___x_729_ = l_Lean_Fmt_Error_partialFormatter;
v___x_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_a_636_);
return v___x_730_;
}
else
{
lean_object* v_disch_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_disch_731_ = l_Lean_Syntax_getArg(v___x_726_, v___x_647_);
lean_dec(v___x_726_);
v___x_732_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__3));
lean_inc(v_disch_731_);
v___x_733_ = l_Lean_Syntax_isOfKind(v_disch_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v_disch_731_);
lean_dec(v_tk_648_);
lean_dec(v_cfg_642_);
lean_dec(v_x_634_);
v___x_734_ = l_Lean_Fmt_Error_partialFormatter;
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v_a_636_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_disch_731_);
v_disch_714_ = v___x_736_;
v___y_715_ = v_a_635_;
v___y_716_ = v_a_636_;
goto v___jp_713_;
}
}
}
else
{
lean_object* v___x_737_; 
lean_dec(v___x_726_);
v___x_737_ = lean_box(0);
v_disch_714_ = v___x_737_;
v___y_715_ = v_a_635_;
v___y_716_ = v_a_636_;
goto v___jp_713_;
}
v___jp_649_:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_mk_empty_array_with_capacity(v___x_641_);
v___x_659_ = lean_array_push(v___x_658_, v_tk_648_);
if (lean_obj_tag(v___y_653_) == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = l_Lean_Fmt_fmtSimpLike(v___x_659_, v_cfg_642_, v___y_654_, v___y_650_, v___y_651_, v___x_660_, v___y_652_, v_loc_x3f_655_, v___y_656_, v___y_657_);
return v___x_661_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_val_662_ = lean_ctor_get(v___y_653_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___y_653_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v___y_653_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_val_662_);
lean_dec(v___y_653_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_val_662_);
v___x_667_ = v_reuseFailAlloc_669_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Fmt_fmtSimpLike(v___x_659_, v_cfg_642_, v___y_654_, v___y_650_, v___y_651_, v___x_667_, v___y_652_, v_loc_x3f_655_, v___y_656_, v___y_657_);
return v___x_668_;
}
}
}
}
v___jp_671_:
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_679_ = lean_unsigned_to_nat(5u);
v___x_680_ = l_Lean_Syntax_getArg(v_x_634_, v___x_679_);
lean_dec(v_x_634_);
v___x_681_ = l_Lean_Syntax_isNone(v___x_680_);
if (v___x_681_ == 0)
{
uint8_t v___x_682_; 
lean_inc(v___x_680_);
v___x_682_ = l_Lean_Syntax_matchesNull(v___x_680_, v___x_641_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v___x_680_);
lean_dec(v_rbTk_x3f_676_);
lean_dec(v_args_x3f_675_);
lean_dec(v_lbTk_x3f_674_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v_tk_648_);
lean_dec(v_cfg_642_);
v___x_683_ = l_Lean_Fmt_Error_partialFormatter;
v___x_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___y_678_);
return v___x_684_;
}
else
{
lean_object* v_loc_x3f_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_loc_x3f_685_ = l_Lean_Syntax_getArg(v___x_680_, v___x_647_);
lean_dec(v___x_680_);
v___x_686_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__9));
lean_inc(v_loc_x3f_685_);
v___x_687_ = l_Lean_Syntax_isOfKind(v_loc_x3f_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v_loc_x3f_685_);
lean_dec(v_rbTk_x3f_676_);
lean_dec(v_args_x3f_675_);
lean_dec(v_lbTk_x3f_674_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v_tk_648_);
lean_dec(v_cfg_642_);
v___x_688_ = l_Lean_Fmt_Error_partialFormatter;
v___x_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___y_678_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v_loc_x3f_685_);
v___y_650_ = v___y_672_;
v___y_651_ = v_lbTk_x3f_674_;
v___y_652_ = v_rbTk_x3f_676_;
v___y_653_ = v_args_x3f_675_;
v___y_654_ = v___y_673_;
v_loc_x3f_655_ = v___x_690_;
v___y_656_ = v___y_677_;
v___y_657_ = v___y_678_;
goto v___jp_649_;
}
}
}
else
{
lean_object* v___x_691_; 
lean_dec(v___x_680_);
v___x_691_ = lean_box(0);
v___y_650_ = v___y_672_;
v___y_651_ = v_lbTk_x3f_674_;
v___y_652_ = v_rbTk_x3f_676_;
v___y_653_ = v_args_x3f_675_;
v___y_654_ = v___y_673_;
v_loc_x3f_655_ = v___x_691_;
v___y_656_ = v___y_677_;
v___y_657_ = v___y_678_;
goto v___jp_649_;
}
}
v___jp_693_:
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_699_ = lean_unsigned_to_nat(4u);
v___x_700_ = l_Lean_Syntax_getArg(v_x_634_, v___x_699_);
v___x_701_ = l_Lean_Syntax_isNone(v___x_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; 
lean_inc(v___x_700_);
v___x_702_ = l_Lean_Syntax_matchesNull(v___x_700_, v___y_694_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v___x_700_);
lean_dec(v_only_x3f_696_);
lean_dec(v___y_695_);
lean_dec(v_tk_648_);
lean_dec(v_cfg_642_);
lean_dec(v_x_634_);
v___x_703_ = l_Lean_Fmt_Error_partialFormatter;
v___x_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___y_698_);
return v___x_704_;
}
else
{
lean_object* v_lbTk_x3f_705_; lean_object* v___x_706_; lean_object* v_rbTk_x3f_707_; lean_object* v_args_x3f_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_lbTk_x3f_705_ = l_Lean_Syntax_getArg(v___x_700_, v___x_647_);
v___x_706_ = l_Lean_Syntax_getArg(v___x_700_, v___x_641_);
v_rbTk_x3f_707_ = l_Lean_Syntax_getArg(v___x_700_, v___x_692_);
lean_dec(v___x_700_);
v_args_x3f_708_ = l_Lean_Syntax_getArgs(v___x_706_);
lean_dec(v___x_706_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v_lbTk_x3f_705_);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_args_x3f_708_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_rbTk_x3f_707_);
v___y_672_ = v_only_x3f_696_;
v___y_673_ = v___y_695_;
v_lbTk_x3f_674_ = v___x_709_;
v_args_x3f_675_ = v___x_710_;
v_rbTk_x3f_676_ = v___x_711_;
v___y_677_ = v___y_697_;
v___y_678_ = v___y_698_;
goto v___jp_671_;
}
}
else
{
lean_object* v___x_712_; 
lean_dec(v___x_700_);
v___x_712_ = lean_box(0);
v___y_672_ = v_only_x3f_696_;
v___y_673_ = v___y_695_;
v_lbTk_x3f_674_ = v___x_712_;
v_args_x3f_675_ = v___x_712_;
v_rbTk_x3f_676_ = v___x_712_;
v___y_677_ = v___y_697_;
v___y_678_ = v___y_698_;
goto v___jp_671_;
}
}
v___jp_713_:
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(3u);
v___x_718_ = l_Lean_Syntax_getArg(v_x_634_, v___x_717_);
v___x_719_ = l_Lean_Syntax_isNone(v___x_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
lean_inc(v___x_718_);
v___x_720_ = l_Lean_Syntax_matchesNull(v___x_718_, v___x_641_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec(v___x_718_);
lean_dec(v_disch_714_);
lean_dec(v_tk_648_);
lean_dec(v_cfg_642_);
lean_dec(v_x_634_);
v___x_721_ = l_Lean_Fmt_Error_partialFormatter;
v___x_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___y_716_);
return v___x_722_;
}
else
{
lean_object* v_only_x3f_723_; lean_object* v___x_724_; 
v_only_x3f_723_ = l_Lean_Syntax_getArg(v___x_718_, v___x_647_);
lean_dec(v___x_718_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_only_x3f_723_);
v___y_694_ = v___x_717_;
v___y_695_ = v_disch_714_;
v_only_x3f_696_ = v___x_724_;
v___y_697_ = v___y_715_;
v___y_698_ = v___y_716_;
goto v___jp_693_;
}
}
else
{
lean_object* v___x_725_; 
lean_dec(v___x_718_);
v___x_725_ = lean_box(0);
v___y_694_ = v___x_717_;
v___y_695_ = v_disch_714_;
v_only_x3f_696_ = v___x_725_;
v___y_697_ = v___y_715_;
v___y_698_ = v___y_716_;
goto v___jp_693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpArith___boxed(lean_object* v_x_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Fmt_fmtSimpArith(v_x_738_, v_a_739_, v_a_740_);
lean_dec_ref(v_a_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1(){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_748_ = l_Lean_Fmt_fmtAttribute;
v___x_749_ = ((lean_object*)(l_Lean_Fmt_fmtSimpArith___closed__1));
v___x_750_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___closed__1));
v___x_751_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpArith___boxed), 3, 0);
v___x_752_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_748_, v___x_749_, v___x_750_, v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1___boxed(lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1();
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpArithBang(lean_object* v_x_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = ((lean_object*)(l_Lean_Fmt_fmtSimpArithBang___closed__1));
lean_inc(v_x_761_);
v___x_765_ = l_Lean_Syntax_isOfKind(v_x_761_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v_x_761_);
v___x_766_ = l_Lean_Fmt_Error_partialFormatter;
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_a_763_);
return v___x_767_;
}
else
{
lean_object* v___x_768_; lean_object* v_cfg_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_768_ = lean_unsigned_to_nat(1u);
v_cfg_769_ = l_Lean_Syntax_getArg(v_x_761_, v___x_768_);
v___x_770_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_769_);
v___x_771_ = l_Lean_Syntax_isOfKind(v_cfg_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v_cfg_769_);
lean_dec(v_x_761_);
v___x_772_ = l_Lean_Fmt_Error_partialFormatter;
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_a_763_);
return v___x_773_;
}
else
{
lean_object* v___x_774_; lean_object* v_tk_775_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v_loc_x3f_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v_lbTk_x3f_801_; lean_object* v_args_x3f_802_; lean_object* v_rbTk_x3f_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___x_819_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v_only_x3f_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v_disch_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v_tk_775_ = l_Lean_Syntax_getArg(v_x_761_, v___x_774_);
v___x_819_ = lean_unsigned_to_nat(2u);
v___x_853_ = l_Lean_Syntax_getArg(v_x_761_, v___x_819_);
v___x_854_ = l_Lean_Syntax_isNone(v___x_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; 
lean_inc(v___x_853_);
v___x_855_ = l_Lean_Syntax_matchesNull(v___x_853_, v___x_768_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec(v___x_853_);
lean_dec(v_tk_775_);
lean_dec(v_cfg_769_);
lean_dec(v_x_761_);
v___x_856_ = l_Lean_Fmt_Error_partialFormatter;
v___x_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v_a_763_);
return v___x_857_;
}
else
{
lean_object* v_disch_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_disch_858_ = l_Lean_Syntax_getArg(v___x_853_, v___x_774_);
lean_dec(v___x_853_);
v___x_859_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__3));
lean_inc(v_disch_858_);
v___x_860_ = l_Lean_Syntax_isOfKind(v_disch_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec(v_disch_858_);
lean_dec(v_tk_775_);
lean_dec(v_cfg_769_);
lean_dec(v_x_761_);
v___x_861_ = l_Lean_Fmt_Error_partialFormatter;
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_a_763_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_disch_858_);
v_disch_841_ = v___x_863_;
v___y_842_ = v_a_762_;
v___y_843_ = v_a_763_;
goto v___jp_840_;
}
}
}
else
{
lean_object* v___x_864_; 
lean_dec(v___x_853_);
v___x_864_ = lean_box(0);
v_disch_841_ = v___x_864_;
v___y_842_ = v_a_762_;
v___y_843_ = v_a_763_;
goto v___jp_840_;
}
v___jp_776_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_768_);
v___x_786_ = lean_array_push(v___x_785_, v_tk_775_);
if (lean_obj_tag(v___y_777_) == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_box(0);
v___x_788_ = l_Lean_Fmt_fmtSimpLike(v___x_786_, v_cfg_769_, v___y_780_, v___y_781_, v___y_779_, v___x_787_, v___y_778_, v_loc_x3f_782_, v___y_783_, v___y_784_);
return v___x_788_;
}
else
{
lean_object* v_val_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_val_789_ = lean_ctor_get(v___y_777_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___y_777_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v___y_777_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_val_789_);
lean_dec(v___y_777_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_val_789_);
v___x_794_ = v_reuseFailAlloc_796_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Fmt_fmtSimpLike(v___x_786_, v_cfg_769_, v___y_780_, v___y_781_, v___y_779_, v___x_794_, v___y_778_, v_loc_x3f_782_, v___y_783_, v___y_784_);
return v___x_795_;
}
}
}
}
v___jp_798_:
{
lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_806_ = lean_unsigned_to_nat(5u);
v___x_807_ = l_Lean_Syntax_getArg(v_x_761_, v___x_806_);
lean_dec(v_x_761_);
v___x_808_ = l_Lean_Syntax_isNone(v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; 
lean_inc(v___x_807_);
v___x_809_ = l_Lean_Syntax_matchesNull(v___x_807_, v___x_768_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v___x_807_);
lean_dec(v_rbTk_x3f_803_);
lean_dec(v_args_x3f_802_);
lean_dec(v_lbTk_x3f_801_);
lean_dec(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v_tk_775_);
lean_dec(v_cfg_769_);
v___x_810_ = l_Lean_Fmt_Error_partialFormatter;
v___x_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___y_805_);
return v___x_811_;
}
else
{
lean_object* v_loc_x3f_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_loc_x3f_812_ = l_Lean_Syntax_getArg(v___x_807_, v___x_774_);
lean_dec(v___x_807_);
v___x_813_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__9));
lean_inc(v_loc_x3f_812_);
v___x_814_ = l_Lean_Syntax_isOfKind(v_loc_x3f_812_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec(v_loc_x3f_812_);
lean_dec(v_rbTk_x3f_803_);
lean_dec(v_args_x3f_802_);
lean_dec(v_lbTk_x3f_801_);
lean_dec(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v_tk_775_);
lean_dec(v_cfg_769_);
v___x_815_ = l_Lean_Fmt_Error_partialFormatter;
v___x_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___y_805_);
return v___x_816_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v_loc_x3f_812_);
v___y_777_ = v_args_x3f_802_;
v___y_778_ = v_rbTk_x3f_803_;
v___y_779_ = v_lbTk_x3f_801_;
v___y_780_ = v___y_799_;
v___y_781_ = v___y_800_;
v_loc_x3f_782_ = v___x_817_;
v___y_783_ = v___y_804_;
v___y_784_ = v___y_805_;
goto v___jp_776_;
}
}
}
else
{
lean_object* v___x_818_; 
lean_dec(v___x_807_);
v___x_818_ = lean_box(0);
v___y_777_ = v_args_x3f_802_;
v___y_778_ = v_rbTk_x3f_803_;
v___y_779_ = v_lbTk_x3f_801_;
v___y_780_ = v___y_799_;
v___y_781_ = v___y_800_;
v_loc_x3f_782_ = v___x_818_;
v___y_783_ = v___y_804_;
v___y_784_ = v___y_805_;
goto v___jp_776_;
}
}
v___jp_820_:
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(4u);
v___x_827_ = l_Lean_Syntax_getArg(v_x_761_, v___x_826_);
v___x_828_ = l_Lean_Syntax_isNone(v___x_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
lean_inc(v___x_827_);
v___x_829_ = l_Lean_Syntax_matchesNull(v___x_827_, v___y_821_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v___x_827_);
lean_dec(v_only_x3f_823_);
lean_dec(v___y_822_);
lean_dec(v_tk_775_);
lean_dec(v_cfg_769_);
lean_dec(v_x_761_);
v___x_830_ = l_Lean_Fmt_Error_partialFormatter;
v___x_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___y_825_);
return v___x_831_;
}
else
{
lean_object* v_lbTk_x3f_832_; lean_object* v___x_833_; lean_object* v_rbTk_x3f_834_; lean_object* v_args_x3f_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_lbTk_x3f_832_ = l_Lean_Syntax_getArg(v___x_827_, v___x_774_);
v___x_833_ = l_Lean_Syntax_getArg(v___x_827_, v___x_768_);
v_rbTk_x3f_834_ = l_Lean_Syntax_getArg(v___x_827_, v___x_819_);
lean_dec(v___x_827_);
v_args_x3f_835_ = l_Lean_Syntax_getArgs(v___x_833_);
lean_dec(v___x_833_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v_lbTk_x3f_832_);
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v_args_x3f_835_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v_rbTk_x3f_834_);
v___y_799_ = v___y_822_;
v___y_800_ = v_only_x3f_823_;
v_lbTk_x3f_801_ = v___x_836_;
v_args_x3f_802_ = v___x_837_;
v_rbTk_x3f_803_ = v___x_838_;
v___y_804_ = v___y_824_;
v___y_805_ = v___y_825_;
goto v___jp_798_;
}
}
else
{
lean_object* v___x_839_; 
lean_dec(v___x_827_);
v___x_839_ = lean_box(0);
v___y_799_ = v___y_822_;
v___y_800_ = v_only_x3f_823_;
v_lbTk_x3f_801_ = v___x_839_;
v_args_x3f_802_ = v___x_839_;
v_rbTk_x3f_803_ = v___x_839_;
v___y_804_ = v___y_824_;
v___y_805_ = v___y_825_;
goto v___jp_798_;
}
}
v___jp_840_:
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_unsigned_to_nat(3u);
v___x_845_ = l_Lean_Syntax_getArg(v_x_761_, v___x_844_);
v___x_846_ = l_Lean_Syntax_isNone(v___x_845_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; 
lean_inc(v___x_845_);
v___x_847_ = l_Lean_Syntax_matchesNull(v___x_845_, v___x_768_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v___x_845_);
lean_dec(v_disch_841_);
lean_dec(v_tk_775_);
lean_dec(v_cfg_769_);
lean_dec(v_x_761_);
v___x_848_ = l_Lean_Fmt_Error_partialFormatter;
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___y_843_);
return v___x_849_;
}
else
{
lean_object* v_only_x3f_850_; lean_object* v___x_851_; 
v_only_x3f_850_ = l_Lean_Syntax_getArg(v___x_845_, v___x_774_);
lean_dec(v___x_845_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v_only_x3f_850_);
v___y_821_ = v___x_844_;
v___y_822_ = v_disch_841_;
v_only_x3f_823_ = v___x_851_;
v___y_824_ = v___y_842_;
v___y_825_ = v___y_843_;
goto v___jp_820_;
}
}
else
{
lean_object* v___x_852_; 
lean_dec(v___x_845_);
v___x_852_ = lean_box(0);
v___y_821_ = v___x_844_;
v___y_822_ = v_disch_841_;
v_only_x3f_823_ = v___x_852_;
v___y_824_ = v___y_842_;
v___y_825_ = v___y_843_;
goto v___jp_820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpArithBang___boxed(lean_object* v_x_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Fmt_fmtSimpArithBang(v_x_865_, v_a_866_, v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1(){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_875_ = l_Lean_Fmt_fmtAttribute;
v___x_876_ = ((lean_object*)(l_Lean_Fmt_fmtSimpArithBang___closed__1));
v___x_877_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___closed__1));
v___x_878_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpArithBang___boxed), 3, 0);
v___x_879_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_875_, v___x_876_, v___x_877_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1___boxed(lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1();
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllAutoUnfold(lean_object* v_x_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1));
lean_inc(v_x_888_);
v___x_892_ = l_Lean_Syntax_isOfKind(v_x_888_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v_x_888_);
v___x_893_ = l_Lean_Fmt_Error_partialFormatter;
v___x_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v_a_890_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; lean_object* v_cfg_896_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_895_ = lean_unsigned_to_nat(1u);
v_cfg_896_ = l_Lean_Syntax_getArg(v_x_888_, v___x_895_);
v___x_908_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_896_);
v___x_909_ = l_Lean_Syntax_isOfKind(v_cfg_896_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec(v_cfg_896_);
lean_dec(v_x_888_);
v___x_910_ = l_Lean_Fmt_Error_partialFormatter;
v___x_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v_a_890_);
return v___x_911_;
}
else
{
lean_object* v___x_912_; lean_object* v_tk_913_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v_lbTk_x3f_917_; lean_object* v_args_x3f_918_; lean_object* v_rbTk_x3f_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___x_933_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v_only_x3f_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v_disch_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_912_ = lean_unsigned_to_nat(0u);
v_tk_913_ = l_Lean_Syntax_getArg(v_x_888_, v___x_912_);
v___x_933_ = lean_unsigned_to_nat(2u);
v___x_967_ = l_Lean_Syntax_getArg(v_x_888_, v___x_933_);
v___x_968_ = l_Lean_Syntax_isNone(v___x_967_);
if (v___x_968_ == 0)
{
uint8_t v___x_969_; 
lean_inc(v___x_967_);
v___x_969_ = l_Lean_Syntax_matchesNull(v___x_967_, v___x_895_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v___x_967_);
lean_dec(v_tk_913_);
lean_dec(v_cfg_896_);
lean_dec(v_x_888_);
v___x_970_ = l_Lean_Fmt_Error_partialFormatter;
v___x_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v_a_890_);
return v___x_971_;
}
else
{
lean_object* v_disch_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_disch_972_ = l_Lean_Syntax_getArg(v___x_967_, v___x_912_);
lean_dec(v___x_967_);
v___x_973_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__3));
lean_inc(v_disch_972_);
v___x_974_ = l_Lean_Syntax_isOfKind(v_disch_972_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v_disch_972_);
lean_dec(v_tk_913_);
lean_dec(v_cfg_896_);
lean_dec(v_x_888_);
v___x_975_ = l_Lean_Fmt_Error_partialFormatter;
v___x_976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v_a_890_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_977_, 0, v_disch_972_);
v_disch_955_ = v___x_977_;
v___y_956_ = v_a_889_;
v___y_957_ = v_a_890_;
goto v___jp_954_;
}
}
}
else
{
lean_object* v___x_978_; 
lean_dec(v___x_967_);
v___x_978_ = lean_box(0);
v_disch_955_ = v___x_978_;
v___y_956_ = v_a_889_;
v___y_957_ = v_a_890_;
goto v___jp_954_;
}
v___jp_914_:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_mk_empty_array_with_capacity(v___x_895_);
v___x_923_ = lean_array_push(v___x_922_, v_tk_913_);
if (lean_obj_tag(v_args_x3f_918_) == 0)
{
lean_object* v___x_924_; 
v___x_924_ = lean_box(0);
v___y_898_ = v___y_921_;
v___y_899_ = v___x_923_;
v___y_900_ = v_lbTk_x3f_917_;
v___y_901_ = v___y_920_;
v___y_902_ = v_rbTk_x3f_919_;
v___y_903_ = v___y_915_;
v___y_904_ = v___y_916_;
v___y_905_ = v___x_924_;
goto v___jp_897_;
}
else
{
lean_object* v_val_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_val_925_ = lean_ctor_get(v_args_x3f_918_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_args_x3f_918_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v_args_x3f_918_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_val_925_);
lean_dec(v_args_x3f_918_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_val_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
v___y_898_ = v___y_921_;
v___y_899_ = v___x_923_;
v___y_900_ = v_lbTk_x3f_917_;
v___y_901_ = v___y_920_;
v___y_902_ = v_rbTk_x3f_919_;
v___y_903_ = v___y_915_;
v___y_904_ = v___y_916_;
v___y_905_ = v___x_930_;
goto v___jp_897_;
}
}
}
}
v___jp_934_:
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = lean_unsigned_to_nat(4u);
v___x_941_ = l_Lean_Syntax_getArg(v_x_888_, v___x_940_);
lean_dec(v_x_888_);
v___x_942_ = l_Lean_Syntax_isNone(v___x_941_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; 
lean_inc(v___x_941_);
v___x_943_ = l_Lean_Syntax_matchesNull(v___x_941_, v___y_936_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v___x_941_);
lean_dec(v_only_x3f_937_);
lean_dec(v___y_935_);
lean_dec(v_tk_913_);
lean_dec(v_cfg_896_);
v___x_944_ = l_Lean_Fmt_Error_partialFormatter;
v___x_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___y_939_);
return v___x_945_;
}
else
{
lean_object* v_lbTk_x3f_946_; lean_object* v___x_947_; lean_object* v_rbTk_x3f_948_; lean_object* v_args_x3f_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_lbTk_x3f_946_ = l_Lean_Syntax_getArg(v___x_941_, v___x_912_);
v___x_947_ = l_Lean_Syntax_getArg(v___x_941_, v___x_895_);
v_rbTk_x3f_948_ = l_Lean_Syntax_getArg(v___x_941_, v___x_933_);
lean_dec(v___x_941_);
v_args_x3f_949_ = l_Lean_Syntax_getArgs(v___x_947_);
lean_dec(v___x_947_);
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v_lbTk_x3f_946_);
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_args_x3f_949_);
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v_rbTk_x3f_948_);
v___y_915_ = v___y_935_;
v___y_916_ = v_only_x3f_937_;
v_lbTk_x3f_917_ = v___x_950_;
v_args_x3f_918_ = v___x_951_;
v_rbTk_x3f_919_ = v___x_952_;
v___y_920_ = v___y_938_;
v___y_921_ = v___y_939_;
goto v___jp_914_;
}
}
else
{
lean_object* v___x_953_; 
lean_dec(v___x_941_);
v___x_953_ = lean_box(0);
v___y_915_ = v___y_935_;
v___y_916_ = v_only_x3f_937_;
v_lbTk_x3f_917_ = v___x_953_;
v_args_x3f_918_ = v___x_953_;
v_rbTk_x3f_919_ = v___x_953_;
v___y_920_ = v___y_938_;
v___y_921_ = v___y_939_;
goto v___jp_914_;
}
}
v___jp_954_:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = lean_unsigned_to_nat(3u);
v___x_959_ = l_Lean_Syntax_getArg(v_x_888_, v___x_958_);
v___x_960_ = l_Lean_Syntax_isNone(v___x_959_);
if (v___x_960_ == 0)
{
uint8_t v___x_961_; 
lean_inc(v___x_959_);
v___x_961_ = l_Lean_Syntax_matchesNull(v___x_959_, v___x_895_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v___x_959_);
lean_dec(v_disch_955_);
lean_dec(v_tk_913_);
lean_dec(v_cfg_896_);
lean_dec(v_x_888_);
v___x_962_ = l_Lean_Fmt_Error_partialFormatter;
v___x_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___y_957_);
return v___x_963_;
}
else
{
lean_object* v_only_x3f_964_; lean_object* v___x_965_; 
v_only_x3f_964_ = l_Lean_Syntax_getArg(v___x_959_, v___x_912_);
lean_dec(v___x_959_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_only_x3f_964_);
v___y_935_ = v_disch_955_;
v___y_936_ = v___x_958_;
v_only_x3f_937_ = v___x_965_;
v___y_938_ = v___y_956_;
v___y_939_ = v___y_957_;
goto v___jp_934_;
}
}
else
{
lean_object* v___x_966_; 
lean_dec(v___x_959_);
v___x_966_ = lean_box(0);
v___y_935_ = v_disch_955_;
v___y_936_ = v___x_958_;
v_only_x3f_937_ = v___x_966_;
v___y_938_ = v___y_956_;
v___y_939_ = v___y_957_;
goto v___jp_934_;
}
}
}
v___jp_897_:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_box(0);
v___x_907_ = l_Lean_Fmt_fmtSimpLike(v___y_899_, v_cfg_896_, v___y_903_, v___y_904_, v___y_900_, v___y_905_, v___y_902_, v___x_906_, v___y_901_, v___y_898_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllAutoUnfold___boxed(lean_object* v_x_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Fmt_fmtSimpAllAutoUnfold(v_x_979_, v_a_980_, v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1(){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_989_ = l_Lean_Fmt_fmtAttribute;
v___x_990_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAllAutoUnfold___closed__1));
v___x_991_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___closed__1));
v___x_992_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpAllAutoUnfold___boxed), 3, 0);
v___x_993_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_989_, v___x_990_, v___x_991_, v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1___boxed(lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1();
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllArith(lean_object* v_x_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAllArith___closed__1));
lean_inc(v_x_1002_);
v___x_1006_ = l_Lean_Syntax_isOfKind(v_x_1002_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec(v_x_1002_);
v___x_1007_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_a_1004_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v_cfg_1010_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v_cfg_1010_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1009_);
v___x_1022_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_1010_);
v___x_1023_ = l_Lean_Syntax_isOfKind(v_cfg_1010_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec(v_cfg_1010_);
lean_dec(v_x_1002_);
v___x_1024_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v_a_1004_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; lean_object* v_tk_1027_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v_lbTk_x3f_1031_; lean_object* v_args_x3f_1032_; lean_object* v_rbTk_x3f_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___x_1047_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v_only_x3f_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v_disch_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1026_ = lean_unsigned_to_nat(0u);
v_tk_1027_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1026_);
v___x_1047_ = lean_unsigned_to_nat(2u);
v___x_1081_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1047_);
v___x_1082_ = l_Lean_Syntax_isNone(v___x_1081_);
if (v___x_1082_ == 0)
{
uint8_t v___x_1083_; 
lean_inc(v___x_1081_);
v___x_1083_ = l_Lean_Syntax_matchesNull(v___x_1081_, v___x_1009_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v___x_1081_);
lean_dec(v_tk_1027_);
lean_dec(v_cfg_1010_);
lean_dec(v_x_1002_);
v___x_1084_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_a_1004_);
return v___x_1085_;
}
else
{
lean_object* v_disch_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_disch_1086_ = l_Lean_Syntax_getArg(v___x_1081_, v___x_1026_);
lean_dec(v___x_1081_);
v___x_1087_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__3));
lean_inc(v_disch_1086_);
v___x_1088_ = l_Lean_Syntax_isOfKind(v_disch_1086_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec(v_disch_1086_);
lean_dec(v_tk_1027_);
lean_dec(v_cfg_1010_);
lean_dec(v_x_1002_);
v___x_1089_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_a_1004_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_disch_1086_);
v_disch_1069_ = v___x_1091_;
v___y_1070_ = v_a_1003_;
v___y_1071_ = v_a_1004_;
goto v___jp_1068_;
}
}
}
else
{
lean_object* v___x_1092_; 
lean_dec(v___x_1081_);
v___x_1092_ = lean_box(0);
v_disch_1069_ = v___x_1092_;
v___y_1070_ = v_a_1003_;
v___y_1071_ = v_a_1004_;
goto v___jp_1068_;
}
v___jp_1028_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_mk_empty_array_with_capacity(v___x_1009_);
v___x_1037_ = lean_array_push(v___x_1036_, v_tk_1027_);
if (lean_obj_tag(v_args_x3f_1032_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(0);
v___y_1012_ = v___y_1029_;
v___y_1013_ = v___y_1035_;
v___y_1014_ = v___y_1034_;
v___y_1015_ = v_rbTk_x3f_1033_;
v___y_1016_ = v___y_1030_;
v___y_1017_ = v_lbTk_x3f_1031_;
v___y_1018_ = v___x_1037_;
v___y_1019_ = v___x_1038_;
goto v___jp_1011_;
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_val_1039_ = lean_ctor_get(v_args_x3f_1032_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_args_x3f_1032_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v_args_x3f_1032_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v_args_x3f_1032_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_val_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
v___y_1012_ = v___y_1029_;
v___y_1013_ = v___y_1035_;
v___y_1014_ = v___y_1034_;
v___y_1015_ = v_rbTk_x3f_1033_;
v___y_1016_ = v___y_1030_;
v___y_1017_ = v_lbTk_x3f_1031_;
v___y_1018_ = v___x_1037_;
v___y_1019_ = v___x_1044_;
goto v___jp_1011_;
}
}
}
}
v___jp_1048_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_unsigned_to_nat(4u);
v___x_1055_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1054_);
lean_dec(v_x_1002_);
v___x_1056_ = l_Lean_Syntax_isNone(v___x_1055_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; 
lean_inc(v___x_1055_);
v___x_1057_ = l_Lean_Syntax_matchesNull(v___x_1055_, v___y_1050_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec(v___x_1055_);
lean_dec(v_only_x3f_1051_);
lean_dec(v___y_1049_);
lean_dec(v_tk_1027_);
lean_dec(v_cfg_1010_);
v___x_1058_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___y_1053_);
return v___x_1059_;
}
else
{
lean_object* v_lbTk_x3f_1060_; lean_object* v___x_1061_; lean_object* v_rbTk_x3f_1062_; lean_object* v_args_x3f_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_lbTk_x3f_1060_ = l_Lean_Syntax_getArg(v___x_1055_, v___x_1026_);
v___x_1061_ = l_Lean_Syntax_getArg(v___x_1055_, v___x_1009_);
v_rbTk_x3f_1062_ = l_Lean_Syntax_getArg(v___x_1055_, v___x_1047_);
lean_dec(v___x_1055_);
v_args_x3f_1063_ = l_Lean_Syntax_getArgs(v___x_1061_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_lbTk_x3f_1060_);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_args_x3f_1063_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_rbTk_x3f_1062_);
v___y_1029_ = v___y_1049_;
v___y_1030_ = v_only_x3f_1051_;
v_lbTk_x3f_1031_ = v___x_1064_;
v_args_x3f_1032_ = v___x_1065_;
v_rbTk_x3f_1033_ = v___x_1066_;
v___y_1034_ = v___y_1052_;
v___y_1035_ = v___y_1053_;
goto v___jp_1028_;
}
}
else
{
lean_object* v___x_1067_; 
lean_dec(v___x_1055_);
v___x_1067_ = lean_box(0);
v___y_1029_ = v___y_1049_;
v___y_1030_ = v_only_x3f_1051_;
v_lbTk_x3f_1031_ = v___x_1067_;
v_args_x3f_1032_ = v___x_1067_;
v_rbTk_x3f_1033_ = v___x_1067_;
v___y_1034_ = v___y_1052_;
v___y_1035_ = v___y_1053_;
goto v___jp_1028_;
}
}
v___jp_1068_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_unsigned_to_nat(3u);
v___x_1073_ = l_Lean_Syntax_getArg(v_x_1002_, v___x_1072_);
v___x_1074_ = l_Lean_Syntax_isNone(v___x_1073_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; 
lean_inc(v___x_1073_);
v___x_1075_ = l_Lean_Syntax_matchesNull(v___x_1073_, v___x_1009_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v___x_1073_);
lean_dec(v_disch_1069_);
lean_dec(v_tk_1027_);
lean_dec(v_cfg_1010_);
lean_dec(v_x_1002_);
v___x_1076_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___y_1071_);
return v___x_1077_;
}
else
{
lean_object* v_only_x3f_1078_; lean_object* v___x_1079_; 
v_only_x3f_1078_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_1026_);
lean_dec(v___x_1073_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_only_x3f_1078_);
v___y_1049_ = v_disch_1069_;
v___y_1050_ = v___x_1072_;
v_only_x3f_1051_ = v___x_1079_;
v___y_1052_ = v___y_1070_;
v___y_1053_ = v___y_1071_;
goto v___jp_1048_;
}
}
else
{
lean_object* v___x_1080_; 
lean_dec(v___x_1073_);
v___x_1080_ = lean_box(0);
v___y_1049_ = v_disch_1069_;
v___y_1050_ = v___x_1072_;
v_only_x3f_1051_ = v___x_1080_;
v___y_1052_ = v___y_1070_;
v___y_1053_ = v___y_1071_;
goto v___jp_1048_;
}
}
}
v___jp_1011_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = l_Lean_Fmt_fmtSimpLike(v___y_1018_, v_cfg_1010_, v___y_1012_, v___y_1016_, v___y_1017_, v___y_1019_, v___y_1015_, v___x_1020_, v___y_1014_, v___y_1013_);
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllArith___boxed(lean_object* v_x_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Fmt_fmtSimpAllArith(v_x_1093_, v_a_1094_, v_a_1095_);
lean_dec_ref(v_a_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1(){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1103_ = l_Lean_Fmt_fmtAttribute;
v___x_1104_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAllArith___closed__1));
v___x_1105_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___closed__1));
v___x_1106_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpAllArith___boxed), 3, 0);
v___x_1107_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1103_, v___x_1104_, v___x_1105_, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1___boxed(lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1();
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllArithBang(lean_object* v_x_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAllArithBang___closed__1));
lean_inc(v_x_1116_);
v___x_1120_ = l_Lean_Syntax_isOfKind(v_x_1116_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec(v_x_1116_);
v___x_1121_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_a_1118_);
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; lean_object* v_cfg_1124_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1123_ = lean_unsigned_to_nat(1u);
v_cfg_1124_ = l_Lean_Syntax_getArg(v_x_1116_, v___x_1123_);
v___x_1136_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_1124_);
v___x_1137_ = l_Lean_Syntax_isOfKind(v_cfg_1124_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_cfg_1124_);
lean_dec(v_x_1116_);
v___x_1138_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v_a_1118_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v_tk_1141_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v_lbTk_x3f_1145_; lean_object* v_args_x3f_1146_; lean_object* v_rbTk_x3f_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___x_1161_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v_only_x3f_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v_disch_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1140_ = lean_unsigned_to_nat(0u);
v_tk_1141_ = l_Lean_Syntax_getArg(v_x_1116_, v___x_1140_);
v___x_1161_ = lean_unsigned_to_nat(2u);
v___x_1195_ = l_Lean_Syntax_getArg(v_x_1116_, v___x_1161_);
v___x_1196_ = l_Lean_Syntax_isNone(v___x_1195_);
if (v___x_1196_ == 0)
{
uint8_t v___x_1197_; 
lean_inc(v___x_1195_);
v___x_1197_ = l_Lean_Syntax_matchesNull(v___x_1195_, v___x_1123_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec(v___x_1195_);
lean_dec(v_tk_1141_);
lean_dec(v_cfg_1124_);
lean_dec(v_x_1116_);
v___x_1198_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_a_1118_);
return v___x_1199_;
}
else
{
lean_object* v_disch_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_disch_1200_ = l_Lean_Syntax_getArg(v___x_1195_, v___x_1140_);
lean_dec(v___x_1195_);
v___x_1201_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__3));
lean_inc(v_disch_1200_);
v___x_1202_ = l_Lean_Syntax_isOfKind(v_disch_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec(v_disch_1200_);
lean_dec(v_tk_1141_);
lean_dec(v_cfg_1124_);
lean_dec(v_x_1116_);
v___x_1203_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v_a_1118_);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_disch_1200_);
v_disch_1183_ = v___x_1205_;
v___y_1184_ = v_a_1117_;
v___y_1185_ = v_a_1118_;
goto v___jp_1182_;
}
}
}
else
{
lean_object* v___x_1206_; 
lean_dec(v___x_1195_);
v___x_1206_ = lean_box(0);
v_disch_1183_ = v___x_1206_;
v___y_1184_ = v_a_1117_;
v___y_1185_ = v_a_1118_;
goto v___jp_1182_;
}
v___jp_1142_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_mk_empty_array_with_capacity(v___x_1123_);
v___x_1151_ = lean_array_push(v___x_1150_, v_tk_1141_);
if (lean_obj_tag(v_args_x3f_1146_) == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_box(0);
v___y_1126_ = v___y_1148_;
v___y_1127_ = v_lbTk_x3f_1145_;
v___y_1128_ = v___y_1143_;
v___y_1129_ = v___y_1149_;
v___y_1130_ = v___y_1144_;
v___y_1131_ = v_rbTk_x3f_1147_;
v___y_1132_ = v___x_1151_;
v___y_1133_ = v___x_1152_;
goto v___jp_1125_;
}
else
{
lean_object* v_val_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_val_1153_ = lean_ctor_get(v_args_x3f_1146_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_args_x3f_1146_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v_args_x3f_1146_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_val_1153_);
lean_dec(v_args_x3f_1146_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_val_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
v___y_1126_ = v___y_1148_;
v___y_1127_ = v_lbTk_x3f_1145_;
v___y_1128_ = v___y_1143_;
v___y_1129_ = v___y_1149_;
v___y_1130_ = v___y_1144_;
v___y_1131_ = v_rbTk_x3f_1147_;
v___y_1132_ = v___x_1151_;
v___y_1133_ = v___x_1158_;
goto v___jp_1125_;
}
}
}
}
v___jp_1162_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = lean_unsigned_to_nat(4u);
v___x_1169_ = l_Lean_Syntax_getArg(v_x_1116_, v___x_1168_);
lean_dec(v_x_1116_);
v___x_1170_ = l_Lean_Syntax_isNone(v___x_1169_);
if (v___x_1170_ == 0)
{
uint8_t v___x_1171_; 
lean_inc(v___x_1169_);
v___x_1171_ = l_Lean_Syntax_matchesNull(v___x_1169_, v___y_1163_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec(v___x_1169_);
lean_dec(v_only_x3f_1165_);
lean_dec(v___y_1164_);
lean_dec(v_tk_1141_);
lean_dec(v_cfg_1124_);
v___x_1172_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v___y_1167_);
return v___x_1173_;
}
else
{
lean_object* v_lbTk_x3f_1174_; lean_object* v___x_1175_; lean_object* v_rbTk_x3f_1176_; lean_object* v_args_x3f_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_lbTk_x3f_1174_ = l_Lean_Syntax_getArg(v___x_1169_, v___x_1140_);
v___x_1175_ = l_Lean_Syntax_getArg(v___x_1169_, v___x_1123_);
v_rbTk_x3f_1176_ = l_Lean_Syntax_getArg(v___x_1169_, v___x_1161_);
lean_dec(v___x_1169_);
v_args_x3f_1177_ = l_Lean_Syntax_getArgs(v___x_1175_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_lbTk_x3f_1174_);
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_args_x3f_1177_);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_rbTk_x3f_1176_);
v___y_1143_ = v___y_1164_;
v___y_1144_ = v_only_x3f_1165_;
v_lbTk_x3f_1145_ = v___x_1178_;
v_args_x3f_1146_ = v___x_1179_;
v_rbTk_x3f_1147_ = v___x_1180_;
v___y_1148_ = v___y_1166_;
v___y_1149_ = v___y_1167_;
goto v___jp_1142_;
}
}
else
{
lean_object* v___x_1181_; 
lean_dec(v___x_1169_);
v___x_1181_ = lean_box(0);
v___y_1143_ = v___y_1164_;
v___y_1144_ = v_only_x3f_1165_;
v_lbTk_x3f_1145_ = v___x_1181_;
v_args_x3f_1146_ = v___x_1181_;
v_rbTk_x3f_1147_ = v___x_1181_;
v___y_1148_ = v___y_1166_;
v___y_1149_ = v___y_1167_;
goto v___jp_1142_;
}
}
v___jp_1182_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_unsigned_to_nat(3u);
v___x_1187_ = l_Lean_Syntax_getArg(v_x_1116_, v___x_1186_);
v___x_1188_ = l_Lean_Syntax_isNone(v___x_1187_);
if (v___x_1188_ == 0)
{
uint8_t v___x_1189_; 
lean_inc(v___x_1187_);
v___x_1189_ = l_Lean_Syntax_matchesNull(v___x_1187_, v___x_1123_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec(v___x_1187_);
lean_dec(v_disch_1183_);
lean_dec(v_tk_1141_);
lean_dec(v_cfg_1124_);
lean_dec(v_x_1116_);
v___x_1190_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v___y_1185_);
return v___x_1191_;
}
else
{
lean_object* v_only_x3f_1192_; lean_object* v___x_1193_; 
v_only_x3f_1192_ = l_Lean_Syntax_getArg(v___x_1187_, v___x_1140_);
lean_dec(v___x_1187_);
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_only_x3f_1192_);
v___y_1163_ = v___x_1186_;
v___y_1164_ = v_disch_1183_;
v_only_x3f_1165_ = v___x_1193_;
v___y_1166_ = v___y_1184_;
v___y_1167_ = v___y_1185_;
goto v___jp_1162_;
}
}
else
{
lean_object* v___x_1194_; 
lean_dec(v___x_1187_);
v___x_1194_ = lean_box(0);
v___y_1163_ = v___x_1186_;
v___y_1164_ = v_disch_1183_;
v_only_x3f_1165_ = v___x_1194_;
v___y_1166_ = v___y_1184_;
v___y_1167_ = v___y_1185_;
goto v___jp_1162_;
}
}
}
v___jp_1125_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Lean_Fmt_fmtSimpLike(v___y_1132_, v_cfg_1124_, v___y_1128_, v___y_1130_, v___y_1127_, v___y_1133_, v___y_1131_, v___x_1134_, v___y_1126_, v___y_1129_);
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpAllArithBang___boxed(lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Fmt_fmtSimpAllArithBang(v_x_1207_, v_a_1208_, v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1(){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1217_ = l_Lean_Fmt_fmtAttribute;
v___x_1218_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAllArithBang___closed__1));
v___x_1219_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___closed__1));
v___x_1220_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpAllArithBang___boxed), 3, 0);
v___x_1221_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1217_, v___x_1218_, v___x_1219_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1___boxed(lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1();
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimpAutoUnfold(lean_object* v_x_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1));
lean_inc(v_x_1230_);
v___x_1234_ = l_Lean_Syntax_isOfKind(v_x_1230_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_x_1230_);
v___x_1235_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_a_1232_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v_cfg_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1237_ = lean_unsigned_to_nat(1u);
v_cfg_1238_ = l_Lean_Syntax_getArg(v_x_1230_, v___x_1237_);
v___x_1239_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__5));
lean_inc(v_cfg_1238_);
v___x_1240_ = l_Lean_Syntax_isOfKind(v_cfg_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec(v_cfg_1238_);
lean_dec(v_x_1230_);
v___x_1241_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1232_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; lean_object* v_tk_1244_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v_loc_x3f_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v_lbTk_x3f_1270_; lean_object* v_args_x3f_1271_; lean_object* v_rbTk_x3f_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___x_1288_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v_only_x3f_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v_disch_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v_tk_1244_ = l_Lean_Syntax_getArg(v_x_1230_, v___x_1243_);
v___x_1288_ = lean_unsigned_to_nat(2u);
v___x_1322_ = l_Lean_Syntax_getArg(v_x_1230_, v___x_1288_);
v___x_1323_ = l_Lean_Syntax_isNone(v___x_1322_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
lean_inc(v___x_1322_);
v___x_1324_ = l_Lean_Syntax_matchesNull(v___x_1322_, v___x_1237_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v___x_1322_);
lean_dec(v_tk_1244_);
lean_dec(v_cfg_1238_);
lean_dec(v_x_1230_);
v___x_1325_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_a_1232_);
return v___x_1326_;
}
else
{
lean_object* v_disch_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_disch_1327_ = l_Lean_Syntax_getArg(v___x_1322_, v___x_1243_);
lean_dec(v___x_1322_);
v___x_1328_ = ((lean_object*)(l_Lean_Fmt_fmtSimpAutoUnfold___closed__3));
lean_inc(v_disch_1327_);
v___x_1329_ = l_Lean_Syntax_isOfKind(v_disch_1327_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v_disch_1327_);
lean_dec(v_tk_1244_);
lean_dec(v_cfg_1238_);
lean_dec(v_x_1230_);
v___x_1330_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v_a_1232_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_disch_1327_);
v_disch_1310_ = v___x_1332_;
v___y_1311_ = v_a_1231_;
v___y_1312_ = v_a_1232_;
goto v___jp_1309_;
}
}
}
else
{
lean_object* v___x_1333_; 
lean_dec(v___x_1322_);
v___x_1333_ = lean_box(0);
v_disch_1310_ = v___x_1333_;
v___y_1311_ = v_a_1231_;
v___y_1312_ = v_a_1232_;
goto v___jp_1309_;
}
v___jp_1245_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_mk_empty_array_with_capacity(v___x_1237_);
v___x_1255_ = lean_array_push(v___x_1254_, v_tk_1244_);
if (lean_obj_tag(v___y_1247_) == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Lean_Fmt_fmtSimpLike(v___x_1255_, v_cfg_1238_, v___y_1249_, v___y_1250_, v___y_1246_, v___x_1256_, v___y_1248_, v_loc_x3f_1251_, v___y_1252_, v___y_1253_);
return v___x_1257_;
}
else
{
lean_object* v_val_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1266_; 
v_val_1258_ = lean_ctor_get(v___y_1247_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___y_1247_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1260_ = v___y_1247_;
v_isShared_1261_ = v_isSharedCheck_1266_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_val_1258_);
lean_dec(v___y_1247_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1266_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_val_1258_);
v___x_1263_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Fmt_fmtSimpLike(v___x_1255_, v_cfg_1238_, v___y_1249_, v___y_1250_, v___y_1246_, v___x_1263_, v___y_1248_, v_loc_x3f_1251_, v___y_1252_, v___y_1253_);
return v___x_1264_;
}
}
}
}
v___jp_1267_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = lean_unsigned_to_nat(5u);
v___x_1276_ = l_Lean_Syntax_getArg(v_x_1230_, v___x_1275_);
lean_dec(v_x_1230_);
v___x_1277_ = l_Lean_Syntax_isNone(v___x_1276_);
if (v___x_1277_ == 0)
{
uint8_t v___x_1278_; 
lean_inc(v___x_1276_);
v___x_1278_ = l_Lean_Syntax_matchesNull(v___x_1276_, v___x_1237_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v___x_1276_);
lean_dec(v_rbTk_x3f_1272_);
lean_dec(v_args_x3f_1271_);
lean_dec(v_lbTk_x3f_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v_tk_1244_);
lean_dec(v_cfg_1238_);
v___x_1279_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v___y_1274_);
return v___x_1280_;
}
else
{
lean_object* v_loc_x3f_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_loc_x3f_1281_ = l_Lean_Syntax_getArg(v___x_1276_, v___x_1243_);
lean_dec(v___x_1276_);
v___x_1282_ = ((lean_object*)(l_Lean_Fmt_fmtErw___closed__9));
lean_inc(v_loc_x3f_1281_);
v___x_1283_ = l_Lean_Syntax_isOfKind(v_loc_x3f_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v_loc_x3f_1281_);
lean_dec(v_rbTk_x3f_1272_);
lean_dec(v_args_x3f_1271_);
lean_dec(v_lbTk_x3f_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v_tk_1244_);
lean_dec(v_cfg_1238_);
v___x_1284_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v___y_1274_);
return v___x_1285_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_loc_x3f_1281_);
v___y_1246_ = v_lbTk_x3f_1270_;
v___y_1247_ = v_args_x3f_1271_;
v___y_1248_ = v_rbTk_x3f_1272_;
v___y_1249_ = v___y_1268_;
v___y_1250_ = v___y_1269_;
v_loc_x3f_1251_ = v___x_1286_;
v___y_1252_ = v___y_1273_;
v___y_1253_ = v___y_1274_;
goto v___jp_1245_;
}
}
}
else
{
lean_object* v___x_1287_; 
lean_dec(v___x_1276_);
v___x_1287_ = lean_box(0);
v___y_1246_ = v_lbTk_x3f_1270_;
v___y_1247_ = v_args_x3f_1271_;
v___y_1248_ = v_rbTk_x3f_1272_;
v___y_1249_ = v___y_1268_;
v___y_1250_ = v___y_1269_;
v_loc_x3f_1251_ = v___x_1287_;
v___y_1252_ = v___y_1273_;
v___y_1253_ = v___y_1274_;
goto v___jp_1245_;
}
}
v___jp_1289_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = lean_unsigned_to_nat(4u);
v___x_1296_ = l_Lean_Syntax_getArg(v_x_1230_, v___x_1295_);
v___x_1297_ = l_Lean_Syntax_isNone(v___x_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; 
lean_inc(v___x_1296_);
v___x_1298_ = l_Lean_Syntax_matchesNull(v___x_1296_, v___y_1291_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v___x_1296_);
lean_dec(v_only_x3f_1292_);
lean_dec(v___y_1290_);
lean_dec(v_tk_1244_);
lean_dec(v_cfg_1238_);
lean_dec(v_x_1230_);
v___x_1299_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___y_1294_);
return v___x_1300_;
}
else
{
lean_object* v_lbTk_x3f_1301_; lean_object* v___x_1302_; lean_object* v_rbTk_x3f_1303_; lean_object* v_args_x3f_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_lbTk_x3f_1301_ = l_Lean_Syntax_getArg(v___x_1296_, v___x_1243_);
v___x_1302_ = l_Lean_Syntax_getArg(v___x_1296_, v___x_1237_);
v_rbTk_x3f_1303_ = l_Lean_Syntax_getArg(v___x_1296_, v___x_1288_);
lean_dec(v___x_1296_);
v_args_x3f_1304_ = l_Lean_Syntax_getArgs(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_lbTk_x3f_1301_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_args_x3f_1304_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_rbTk_x3f_1303_);
v___y_1268_ = v___y_1290_;
v___y_1269_ = v_only_x3f_1292_;
v_lbTk_x3f_1270_ = v___x_1305_;
v_args_x3f_1271_ = v___x_1306_;
v_rbTk_x3f_1272_ = v___x_1307_;
v___y_1273_ = v___y_1293_;
v___y_1274_ = v___y_1294_;
goto v___jp_1267_;
}
}
else
{
lean_object* v___x_1308_; 
lean_dec(v___x_1296_);
v___x_1308_ = lean_box(0);
v___y_1268_ = v___y_1290_;
v___y_1269_ = v_only_x3f_1292_;
v_lbTk_x3f_1270_ = v___x_1308_;
v_args_x3f_1271_ = v___x_1308_;
v_rbTk_x3f_1272_ = v___x_1308_;
v___y_1273_ = v___y_1293_;
v___y_1274_ = v___y_1294_;
goto v___jp_1267_;
}
}
v___jp_1309_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_unsigned_to_nat(3u);
v___x_1314_ = l_Lean_Syntax_getArg(v_x_1230_, v___x_1313_);
v___x_1315_ = l_Lean_Syntax_isNone(v___x_1314_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; 
lean_inc(v___x_1314_);
v___x_1316_ = l_Lean_Syntax_matchesNull(v___x_1314_, v___x_1237_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec(v___x_1314_);
lean_dec(v_disch_1310_);
lean_dec(v_tk_1244_);
lean_dec(v_cfg_1238_);
lean_dec(v_x_1230_);
v___x_1317_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___y_1312_);
return v___x_1318_;
}
else
{
lean_object* v_only_x3f_1319_; lean_object* v___x_1320_; 
v_only_x3f_1319_ = l_Lean_Syntax_getArg(v___x_1314_, v___x_1243_);
lean_dec(v___x_1314_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_only_x3f_1319_);
v___y_1290_ = v_disch_1310_;
v___y_1291_ = v___x_1313_;
v_only_x3f_1292_ = v___x_1320_;
v___y_1293_ = v___y_1311_;
v___y_1294_ = v___y_1312_;
goto v___jp_1289_;
}
}
else
{
lean_object* v___x_1321_; 
lean_dec(v___x_1314_);
v___x_1321_ = lean_box(0);
v___y_1290_ = v_disch_1310_;
v___y_1291_ = v___x_1313_;
v_only_x3f_1292_ = v___x_1321_;
v___y_1293_ = v___y_1311_;
v___y_1294_ = v___y_1312_;
goto v___jp_1289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimpAutoUnfold___boxed(lean_object* v_x_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Fmt_fmtDSimpAutoUnfold(v_x_1334_, v_a_1335_, v_a_1336_);
lean_dec_ref(v_a_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1(){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1344_ = l_Lean_Fmt_fmtAttribute;
v___x_1345_ = ((lean_object*)(l_Lean_Fmt_fmtDSimpAutoUnfold___closed__1));
v___x_1346_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___closed__1));
v___x_1347_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDSimpAutoUnfold___boxed), 3, 0);
v___x_1348_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1344_, v___x_1345_, v___x_1346_, v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1___boxed(lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1();
return v_res_1350_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Meta(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrec___regBuiltin_Lean_Fmt_fmtEvalPrec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtEvalPrio___regBuiltin_Lean_Fmt_fmtEvalPrio__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtErw___regBuiltin_Lean_Fmt_fmtErw__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllKind___regBuiltin_Lean_Fmt_fmtSimpAllKind__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDsimpKind___regBuiltin_Lean_Fmt_fmtDsimpKind__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDeclareSimpLikeTactic___regBuiltin_Lean_Fmt_fmtDeclareSimpLikeTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAutoUnfold__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArith___regBuiltin_Lean_Fmt_fmtSimpArith__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpArithBang___regBuiltin_Lean_Fmt_fmtSimpArithBang__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllAutoUnfold___regBuiltin_Lean_Fmt_fmtSimpAllAutoUnfold__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArith___regBuiltin_Lean_Fmt_fmtSimpAllArith__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtSimpAllArithBang___regBuiltin_Lean_Fmt_fmtSimpAllArithBang__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Meta_0__Lean_Fmt_fmtDSimpAutoUnfold___regBuiltin_Lean_Fmt_fmtDSimpAutoUnfold__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Meta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Meta(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Meta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Meta(builtin);
}
#ifdef __cplusplus
}
#endif
