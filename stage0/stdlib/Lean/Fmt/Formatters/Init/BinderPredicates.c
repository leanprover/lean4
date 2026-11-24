// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.BinderPredicates
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.Parser.Term meta import Init.BinderPredicates import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_quantifierFmtAttribute;
lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSatisfiesBinderPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "termSatisfies_binder_pred%__"};
static const lean_object* l_Lean_Fmt_fmtSatisfiesBinderPred___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtSatisfiesBinderPred___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSatisfiesBinderPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(35, 32, 166, 185, 227, 132, 228, 81)}};
static const lean_object* l_Lean_Fmt_fmtSatisfiesBinderPred___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSatisfiesBinderPred(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSatisfiesBinderPred___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtSatisfiesBinderPred"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(98, 143, 102, 93, 121, 201, 7, 223)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredPrefix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredGt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binderPred>_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredGt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredGt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredGt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredGt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredGt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredGt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 244, 246, 184, 111, 78, 213, 47)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredGt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredGt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredGt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredGt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtBinderPredGt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 144, 153, 21, 92, 35, 76, 118)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredGe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred≥_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredGe___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredGe___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredGe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredGe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredGe___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredGe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 139, 67, 46, 49, 133, 157, 246)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredGe___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredGe___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredGe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredGe___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtBinderPredGe"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 71, 223, 175, 138, 73, 253, 99)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binderPred<_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredLt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredLt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredLt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredLt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 122, 58, 108, 39, 32, 195, 29)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredLt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredLt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredLt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtBinderPredLt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 156, 219, 162, 22, 134, 123, 209)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredLe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred≤_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredLe___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredLe___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredLe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredLe___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredLe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 254, 52, 209, 56, 53, 218, 188)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredLe___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredLe___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredLe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredLe___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtBinderPredLe"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 71, 25, 89, 70, 112, 11, 227)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredNe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred≠_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredNe___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredNe___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredNe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredNe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredNe___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredNe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 40, 245, 52, 138, 78, 140, 19)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredNe___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredNe___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredNe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredNe___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtBinderPredNe"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 46, 73, 54, 128, 31, 253, 112)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredMem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred∈_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredMem___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredMem___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredMem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredMem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredMem___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredMem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 164, 254, 63, 76, 57, 126, 92)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredMem___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredMem___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredMem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredMem___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtBinderPredMem"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 121, 153, 51, 198, 88, 66, 174)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredNotMem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred∉_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredNotMem___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredNotMem___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredNotMem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredNotMem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredNotMem___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredNotMem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 253, 164, 249, 200, 108, 121, 70)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredNotMem___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredNotMem___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredNotMem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredNotMem___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtBinderPredNotMem"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 97, 48, 140, 108, 54, 225, 54)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredSubset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred⊆_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredSubset___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredSubset___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredSubset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredSubset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredSubset___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredSubset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 23, 43, 221, 193, 123, 248, 62)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredSubset___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredSubset___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSubset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSubset___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtBinderPredSubset"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 158, 203, 155, 103, 212, 233, 6)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredSSubset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred⊂_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredSSubset___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredSSubset___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredSSubset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredSSubset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredSSubset___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredSSubset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 93, 221, 41, 188, 55, 153, 107)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredSSubset___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredSSubset___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSSubset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSSubset___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtBinderPredSSubset"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 98, 99, 97, 24, 248, 205, 24)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredSuperset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred⊇_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredSuperset___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredSuperset___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredSuperset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredSuperset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredSuperset___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredSuperset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 205, 109, 198, 229, 195, 21, 21)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredSuperset___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredSuperset___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSuperset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSuperset___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtBinderPredSuperset"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 102, 43, 21, 58, 218, 186, 79)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredSSuperset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "binderPred⊃_"};
static const lean_object* l_Lean_Fmt_fmtBinderPredSSuperset___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredSSuperset___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredSSuperset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredSSuperset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredSSuperset___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderPredSSuperset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 228, 155, 154, 179, 5, 240, 181)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredSSuperset___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredSSuperset___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSSuperset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSSuperset___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtBinderPredSSuperset"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 120, 56, 173, 146, 34, 33, 150)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtForallBinderPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "term∀__,_"};
static const lean_object* l_Lean_Fmt_fmtForallBinderPred___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtForallBinderPred___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtForallBinderPred___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtForallBinderPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtForallBinderPred___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtForallBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 16, 227, 203, 159, 8, 82, 19)}};
static const lean_object* l_Lean_Fmt_fmtForallBinderPred___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtForallBinderPred___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtForallBinderPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Fmt_fmtForallBinderPred___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtForallBinderPred___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtForallBinderPred___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtForallBinderPred___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtForallBinderPred___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtForallBinderPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Fmt_fmtForallBinderPred___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtForallBinderPred___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtForallBinderPred(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtForallBinderPred"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 116, 237, 220, 149, 120, 239, 186)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExistsBinderPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "term∃__,_"};
static const lean_object* l_Lean_Fmt_fmtExistsBinderPred___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExistsBinderPred___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExistsBinderPred___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExistsBinderPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExistsBinderPred___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtExistsBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 165, 221, 98, 134, 231, 221, 237)}};
static const lean_object* l_Lean_Fmt_fmtExistsBinderPred___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExistsBinderPred___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExistsBinderPred(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtExistsBinderPred"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSatisfiesBinderPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 166, 229, 1, 87, 52, 147, 118)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSatisfiesBinderPred(lean_object* v_x_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lean_Fmt_fmtSatisfiesBinderPred___closed__2));
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
lean_object* v___x_13_; lean_object* v_satisfiesBinderPredTk_14_; lean_object* v___x_15_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v_satisfiesBinderPredTk_14_ = l_Lean_Syntax_getArg(v_x_6_, v___x_13_);
v___x_15_ = l_Lean_Fmt_fmt(v_satisfiesBinderPredTk_14_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_pred_21_; lean_object* v___x_22_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v___x_15_, 1);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_15_, 2);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = l_Lean_Syntax_getArg(v_x_6_, v___x_18_);
v___x_20_ = lean_unsigned_to_nat(2u);
v_pred_21_ = l_Lean_Syntax_getArg(v_x_6_, v___x_20_);
lean_dec(v_x_6_);
v___x_22_ = l_Lean_Fmt_fmtWithBinderPred(v___x_19_, v_pred_21_, v_a_7_, v_a_17_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_37_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_a_24_ = lean_ctor_get(v___x_22_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_37_ == 0)
{
v___x_26_ = v___x_22_;
v_isShared_27_ = v_isSharedCheck_37_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_37_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_28_ = lean_mk_empty_array_with_capacity(v___x_20_);
v___x_29_ = lean_array_push(v___x_28_, v_a_16_);
v___x_30_ = lean_array_push(v___x_29_, v_a_23_);
v___x_31_ = 0;
v___x_32_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_32_, 0, v___x_10_);
lean_ctor_set_uint8(v___x_32_, 1, v___x_31_);
lean_ctor_set_uint8(v___x_32_, 2, v___x_31_);
lean_ctor_set_uint8(v___x_32_, 3, v___x_31_);
v___x_33_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_30_, v___x_32_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_33_);
v___x_35_ = v___x_26_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_a_24_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_dec(v_a_16_);
return v___x_22_;
}
}
else
{
lean_dec(v_x_6_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSatisfiesBinderPred___boxed(lean_object* v_x_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Fmt_fmtSatisfiesBinderPred(v_x_38_, v_a_39_, v_a_40_);
lean_dec_ref(v_a_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1(){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_49_ = l_Lean_Fmt_fmtAttribute;
v___x_50_ = ((lean_object*)(l_Lean_Fmt_fmtSatisfiesBinderPred___closed__2));
v___x_51_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___closed__2));
v___x_52_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSatisfiesBinderPred___boxed), 3, 0);
v___x_53_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_49_, v___x_50_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1___boxed(lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1();
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredPrefix(lean_object* v_opTk_56_, lean_object* v_rhs_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Fmt_fmt(v_opTk_56_, v_a_58_, v_a_59_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___x_63_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
v_a_62_ = lean_ctor_get(v___x_60_, 1);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_60_, 2);
v___x_63_ = l_Lean_Fmt_fmt(v_rhs_57_, v_a_58_, v_a_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_74_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_a_65_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_74_ == 0)
{
v___x_67_ = v___x_63_;
v_isShared_68_ = v_isSharedCheck_74_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_74_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_69_ = 2;
v___x_70_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_61_, v_a_64_, v___x_69_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_70_);
v___x_72_ = v___x_67_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_a_65_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_dec(v_a_61_);
return v___x_63_;
}
}
else
{
lean_dec(v_rhs_57_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredPrefix___boxed(lean_object* v_opTk_75_, lean_object* v_rhs_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_75_, v_rhs_76_, v_a_77_, v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredGt(lean_object* v_x_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredGt___closed__1));
lean_inc(v_x_84_);
v___x_88_ = l_Lean_Syntax_isOfKind(v_x_84_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_x_84_);
v___x_89_ = l_Lean_Fmt_Error_partialFormatter;
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_a_86_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_opTk_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v_opTk_92_ = l_Lean_Syntax_getArg(v_x_84_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = l_Lean_Syntax_getArg(v_x_84_, v___x_93_);
lean_dec(v_x_84_);
v___x_95_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_92_, v___x_94_, v_a_85_, v_a_86_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredGt___boxed(lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Fmt_fmtBinderPredGt(v_x_96_, v_a_97_, v_a_98_);
lean_dec_ref(v_a_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1(){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_106_ = l_Lean_Fmt_fmtAttribute;
v___x_107_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredGt___closed__1));
v___x_108_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___closed__1));
v___x_109_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredGt___boxed), 3, 0);
v___x_110_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_106_, v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1___boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredGe(lean_object* v_x_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredGe___closed__1));
lean_inc(v_x_117_);
v___x_121_ = l_Lean_Syntax_isOfKind(v_x_117_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_x_117_);
v___x_122_ = l_Lean_Fmt_Error_partialFormatter;
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_a_119_);
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v_opTk_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v_opTk_125_ = l_Lean_Syntax_getArg(v_x_117_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = l_Lean_Syntax_getArg(v_x_117_, v___x_126_);
lean_dec(v_x_117_);
v___x_128_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_125_, v___x_127_, v_a_118_, v_a_119_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredGe___boxed(lean_object* v_x_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Fmt_fmtBinderPredGe(v_x_129_, v_a_130_, v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1(){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = l_Lean_Fmt_fmtAttribute;
v___x_140_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredGe___closed__1));
v___x_141_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___closed__1));
v___x_142_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredGe___boxed), 3, 0);
v___x_143_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_139_, v___x_140_, v___x_141_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1___boxed(lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1();
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredLt(lean_object* v_x_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredLt___closed__1));
lean_inc(v_x_150_);
v___x_154_ = l_Lean_Syntax_isOfKind(v_x_150_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_x_150_);
v___x_155_ = l_Lean_Fmt_Error_partialFormatter;
v___x_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_a_152_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; lean_object* v_opTk_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v_opTk_158_ = l_Lean_Syntax_getArg(v_x_150_, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = l_Lean_Syntax_getArg(v_x_150_, v___x_159_);
lean_dec(v_x_150_);
v___x_161_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_158_, v___x_160_, v_a_151_, v_a_152_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredLt___boxed(lean_object* v_x_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Fmt_fmtBinderPredLt(v_x_162_, v_a_163_, v_a_164_);
lean_dec_ref(v_a_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1(){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_172_ = l_Lean_Fmt_fmtAttribute;
v___x_173_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredLt___closed__1));
v___x_174_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___closed__1));
v___x_175_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredLt___boxed), 3, 0);
v___x_176_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_172_, v___x_173_, v___x_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1___boxed(lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1();
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredLe(lean_object* v_x_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredLe___closed__1));
lean_inc(v_x_183_);
v___x_187_ = l_Lean_Syntax_isOfKind(v_x_183_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_x_183_);
v___x_188_ = l_Lean_Fmt_Error_partialFormatter;
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_185_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v_opTk_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v_opTk_191_ = l_Lean_Syntax_getArg(v_x_183_, v___x_190_);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = l_Lean_Syntax_getArg(v_x_183_, v___x_192_);
lean_dec(v_x_183_);
v___x_194_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_191_, v___x_193_, v_a_184_, v_a_185_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredLe___boxed(lean_object* v_x_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Fmt_fmtBinderPredLe(v_x_195_, v_a_196_, v_a_197_);
lean_dec_ref(v_a_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1(){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_205_ = l_Lean_Fmt_fmtAttribute;
v___x_206_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredLe___closed__1));
v___x_207_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___closed__1));
v___x_208_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredLe___boxed), 3, 0);
v___x_209_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_205_, v___x_206_, v___x_207_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1___boxed(lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1();
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredNe(lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredNe___closed__1));
lean_inc(v_x_216_);
v___x_220_ = l_Lean_Syntax_isOfKind(v_x_216_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_x_216_);
v___x_221_ = l_Lean_Fmt_Error_partialFormatter;
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_a_218_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v_opTk_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v_opTk_224_ = l_Lean_Syntax_getArg(v_x_216_, v___x_223_);
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = l_Lean_Syntax_getArg(v_x_216_, v___x_225_);
lean_dec(v_x_216_);
v___x_227_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_224_, v___x_226_, v_a_217_, v_a_218_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredNe___boxed(lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Fmt_fmtBinderPredNe(v_x_228_, v_a_229_, v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1(){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_238_ = l_Lean_Fmt_fmtAttribute;
v___x_239_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredNe___closed__1));
v___x_240_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___closed__1));
v___x_241_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredNe___boxed), 3, 0);
v___x_242_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_238_, v___x_239_, v___x_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1___boxed(lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1();
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredMem(lean_object* v_x_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredMem___closed__1));
lean_inc(v_x_249_);
v___x_253_ = l_Lean_Syntax_isOfKind(v_x_249_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_x_249_);
v___x_254_ = l_Lean_Fmt_Error_partialFormatter;
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_251_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v_opTk_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v_opTk_257_ = l_Lean_Syntax_getArg(v_x_249_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_249_, v___x_258_);
lean_dec(v_x_249_);
v___x_260_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_257_, v___x_259_, v_a_250_, v_a_251_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredMem___boxed(lean_object* v_x_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Fmt_fmtBinderPredMem(v_x_261_, v_a_262_, v_a_263_);
lean_dec_ref(v_a_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1(){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_271_ = l_Lean_Fmt_fmtAttribute;
v___x_272_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredMem___closed__1));
v___x_273_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___closed__1));
v___x_274_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredMem___boxed), 3, 0);
v___x_275_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_271_, v___x_272_, v___x_273_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1___boxed(lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1();
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredNotMem(lean_object* v_x_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredNotMem___closed__1));
lean_inc(v_x_282_);
v___x_286_ = l_Lean_Syntax_isOfKind(v_x_282_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_x_282_);
v___x_287_ = l_Lean_Fmt_Error_partialFormatter;
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_a_284_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v_opTk_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v_opTk_290_ = l_Lean_Syntax_getArg(v_x_282_, v___x_289_);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = l_Lean_Syntax_getArg(v_x_282_, v___x_291_);
lean_dec(v_x_282_);
v___x_293_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_290_, v___x_292_, v_a_283_, v_a_284_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredNotMem___boxed(lean_object* v_x_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Fmt_fmtBinderPredNotMem(v_x_294_, v_a_295_, v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1(){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_304_ = l_Lean_Fmt_fmtAttribute;
v___x_305_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredNotMem___closed__1));
v___x_306_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___closed__1));
v___x_307_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredNotMem___boxed), 3, 0);
v___x_308_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_304_, v___x_305_, v___x_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1___boxed(lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1();
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSubset(lean_object* v_x_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredSubset___closed__1));
lean_inc(v_x_315_);
v___x_319_ = l_Lean_Syntax_isOfKind(v_x_315_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v_x_315_);
v___x_320_ = l_Lean_Fmt_Error_partialFormatter;
v___x_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_a_317_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v_opTk_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v_opTk_323_ = l_Lean_Syntax_getArg(v_x_315_, v___x_322_);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = l_Lean_Syntax_getArg(v_x_315_, v___x_324_);
lean_dec(v_x_315_);
v___x_326_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_323_, v___x_325_, v_a_316_, v_a_317_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSubset___boxed(lean_object* v_x_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Fmt_fmtBinderPredSubset(v_x_327_, v_a_328_, v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1(){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_337_ = l_Lean_Fmt_fmtAttribute;
v___x_338_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredSubset___closed__1));
v___x_339_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___closed__1));
v___x_340_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredSubset___boxed), 3, 0);
v___x_341_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_337_, v___x_338_, v___x_339_, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1___boxed(lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1();
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSSubset(lean_object* v_x_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredSSubset___closed__1));
lean_inc(v_x_348_);
v___x_352_ = l_Lean_Syntax_isOfKind(v_x_348_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_x_348_);
v___x_353_ = l_Lean_Fmt_Error_partialFormatter;
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_a_350_);
return v___x_354_;
}
else
{
lean_object* v___x_355_; lean_object* v_opTk_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v_opTk_356_ = l_Lean_Syntax_getArg(v_x_348_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = l_Lean_Syntax_getArg(v_x_348_, v___x_357_);
lean_dec(v_x_348_);
v___x_359_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_356_, v___x_358_, v_a_349_, v_a_350_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSSubset___boxed(lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Fmt_fmtBinderPredSSubset(v_x_360_, v_a_361_, v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1(){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_370_ = l_Lean_Fmt_fmtAttribute;
v___x_371_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredSSubset___closed__1));
v___x_372_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___closed__1));
v___x_373_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredSSubset___boxed), 3, 0);
v___x_374_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_370_, v___x_371_, v___x_372_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1___boxed(lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1();
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSuperset(lean_object* v_x_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredSuperset___closed__1));
lean_inc(v_x_381_);
v___x_385_ = l_Lean_Syntax_isOfKind(v_x_381_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_x_381_);
v___x_386_ = l_Lean_Fmt_Error_partialFormatter;
v___x_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_a_383_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v_opTk_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v_opTk_389_ = l_Lean_Syntax_getArg(v_x_381_, v___x_388_);
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = l_Lean_Syntax_getArg(v_x_381_, v___x_390_);
lean_dec(v_x_381_);
v___x_392_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_389_, v___x_391_, v_a_382_, v_a_383_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSuperset___boxed(lean_object* v_x_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Fmt_fmtBinderPredSuperset(v_x_393_, v_a_394_, v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1(){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_403_ = l_Lean_Fmt_fmtAttribute;
v___x_404_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredSuperset___closed__1));
v___x_405_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___closed__1));
v___x_406_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredSuperset___boxed), 3, 0);
v___x_407_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_403_, v___x_404_, v___x_405_, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1___boxed(lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1();
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSSuperset(lean_object* v_x_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredSSuperset___closed__1));
lean_inc(v_x_414_);
v___x_418_ = l_Lean_Syntax_isOfKind(v_x_414_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_x_414_);
v___x_419_ = l_Lean_Fmt_Error_partialFormatter;
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_a_416_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v_opTk_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v_opTk_422_ = l_Lean_Syntax_getArg(v_x_414_, v___x_421_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = l_Lean_Syntax_getArg(v_x_414_, v___x_423_);
lean_dec(v_x_414_);
v___x_425_ = l_Lean_Fmt_fmtBinderPredPrefix(v_opTk_422_, v___x_424_, v_a_415_, v_a_416_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredSSuperset___boxed(lean_object* v_x_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Fmt_fmtBinderPredSSuperset(v_x_426_, v_a_427_, v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1(){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_436_ = l_Lean_Fmt_fmtAttribute;
v___x_437_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredSSuperset___closed__1));
v___x_438_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___closed__1));
v___x_439_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredSSuperset___boxed), 3, 0);
v___x_440_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_436_, v___x_437_, v___x_438_, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1___boxed(lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1();
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtForallBinderPred(lean_object* v_x_451_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Fmt_fmtForallBinderPred___closed__1));
lean_inc(v_x_451_);
v___x_453_ = l_Lean_Syntax_isOfKind(v_x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec(v_x_451_);
v___x_454_ = lean_box(0);
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = l_Lean_Syntax_getArg(v_x_451_, v___x_455_);
v___x_457_ = ((lean_object*)(l_Lean_Fmt_fmtForallBinderPred___closed__3));
lean_inc(v___x_456_);
v___x_458_ = l_Lean_Syntax_isOfKind(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v___x_456_);
lean_dec(v_x_451_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v_forallTk_461_; lean_object* v___x_462_; lean_object* v_pred_463_; lean_object* v___x_464_; lean_object* v_commaTk_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v_forallTk_461_ = l_Lean_Syntax_getArg(v_x_451_, v___x_460_);
v___x_462_ = lean_unsigned_to_nat(2u);
v_pred_463_ = l_Lean_Syntax_getArg(v_x_451_, v___x_462_);
v___x_464_ = lean_unsigned_to_nat(3u);
v_commaTk_465_ = l_Lean_Syntax_getArg(v_x_451_, v___x_464_);
v___x_466_ = lean_unsigned_to_nat(4u);
v___x_467_ = l_Lean_Syntax_getArg(v_x_451_, v___x_466_);
lean_dec(v_x_451_);
v___x_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_456_);
lean_ctor_set(v___x_468_, 1, v_pred_463_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_470_, 0, v_forallTk_461_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_469_);
lean_ctor_set(v___x_470_, 3, v___x_469_);
lean_ctor_set(v___x_470_, 4, v_commaTk_465_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_467_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1(){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_479_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_480_ = ((lean_object*)(l_Lean_Fmt_fmtForallBinderPred___closed__1));
v___x_481_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___closed__1));
v___x_482_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtForallBinderPred), 1, 0);
v___x_483_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_479_, v___x_480_, v___x_481_, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1___boxed(lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1();
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExistsBinderPred(lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Fmt_fmtExistsBinderPred___closed__1));
lean_inc(v_x_490_);
v___x_492_ = l_Lean_Syntax_isOfKind(v_x_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
lean_dec(v_x_490_);
v___x_493_ = lean_box(0);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = l_Lean_Syntax_getArg(v_x_490_, v___x_494_);
v___x_496_ = ((lean_object*)(l_Lean_Fmt_fmtForallBinderPred___closed__3));
lean_inc(v___x_495_);
v___x_497_ = l_Lean_Syntax_isOfKind(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v___x_495_);
lean_dec(v_x_490_);
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v_existsTk_500_; lean_object* v___x_501_; lean_object* v_pred_502_; lean_object* v___x_503_; lean_object* v_commaTk_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v_existsTk_500_ = l_Lean_Syntax_getArg(v_x_490_, v___x_499_);
v___x_501_ = lean_unsigned_to_nat(2u);
v_pred_502_ = l_Lean_Syntax_getArg(v_x_490_, v___x_501_);
v___x_503_ = lean_unsigned_to_nat(3u);
v_commaTk_504_ = l_Lean_Syntax_getArg(v_x_490_, v___x_503_);
v___x_505_ = lean_unsigned_to_nat(4u);
v___x_506_ = l_Lean_Syntax_getArg(v_x_490_, v___x_505_);
lean_dec(v_x_490_);
v___x_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_495_);
lean_ctor_set(v___x_507_, 1, v_pred_502_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_509_, 0, v_existsTk_500_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_508_);
lean_ctor_set(v___x_509_, 3, v___x_508_);
lean_ctor_set(v___x_509_, 4, v_commaTk_504_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_506_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1(){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_518_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_519_ = ((lean_object*)(l_Lean_Fmt_fmtExistsBinderPred___closed__1));
v___x_520_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___closed__1));
v___x_521_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExistsBinderPred), 1, 0);
v___x_522_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_518_, v___x_519_, v___x_520_, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1___boxed(lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1();
return v_res_524_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_BinderPredicates(uint8_t builtin) {
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
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtSatisfiesBinderPred___regBuiltin_Lean_Fmt_fmtSatisfiesBinderPred__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGt___regBuiltin_Lean_Fmt_fmtBinderPredGt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredGe___regBuiltin_Lean_Fmt_fmtBinderPredGe__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLt___regBuiltin_Lean_Fmt_fmtBinderPredLt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredLe___regBuiltin_Lean_Fmt_fmtBinderPredLe__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNe___regBuiltin_Lean_Fmt_fmtBinderPredNe__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredMem___regBuiltin_Lean_Fmt_fmtBinderPredMem__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredNotMem___regBuiltin_Lean_Fmt_fmtBinderPredNotMem__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSubset___regBuiltin_Lean_Fmt_fmtBinderPredSubset__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSubset___regBuiltin_Lean_Fmt_fmtBinderPredSSubset__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSuperset__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtBinderPredSSuperset___regBuiltin_Lean_Fmt_fmtBinderPredSSuperset__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtForallBinderPred___regBuiltin_Lean_Fmt_fmtForallBinderPred__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_BinderPredicates_0__Lean_Fmt_fmtExistsBinderPred___regBuiltin_Lean_Fmt_fmtExistsBinderPred__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_BinderPredicates(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_BinderPredicates(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_BinderPredicates(builtin);
}
#ifdef __cplusplus
}
#endif
