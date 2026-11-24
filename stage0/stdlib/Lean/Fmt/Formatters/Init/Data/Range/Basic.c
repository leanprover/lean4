// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Data.Range.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Data.Range.Basic import Init.Data
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Legacy"};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Range"};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term[:_]"};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 247, 114, 105, 22, 2, 212, 24)}};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtLegacyRangeUpperBound"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 247, 0, 64, 7, 86, 163, 81)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLegacyRangeBounds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term[_:_]"};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeBounds___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeBounds___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeBounds___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeBounds___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeBounds___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeBounds___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeBounds___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeBounds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeBounds___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeBounds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 227, 143, 95, 3, 88, 200, 110)}};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeBounds___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeBounds___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeBounds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeBounds___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtLegacyRangeBounds"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 206, 95, 129, 20, 77, 48, 38)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term[:_:_]"};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 39, 16, 99, 27, 138, 138, 190)}};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "fmtLegacyRangeUpperBoundWithStep"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 179, 79, 243, 130, 203, 191, 121)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term[_:_:_]"};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 172, 42, 253, 230, 203, 52, 54)}};
static const lean_object* l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeBoundsWithStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "fmtLegacyRangeBoundsWithStep"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 137, 57, 135, 140, 14, 231, 227)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4));
lean_inc(v_x_10_);
v___x_14_ = l_Lean_Syntax_isOfKind(v_x_10_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec(v_x_10_);
v___x_15_ = l_Lean_Fmt_Error_partialFormatter;
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_a_12_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v_lbTk_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v_lbTk_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
v___x_19_ = l_Lean_Fmt_fmt(v_lbTk_18_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; lean_object* v_colonTk_23_; lean_object* v___x_24_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_19_, 2);
v___x_22_ = lean_unsigned_to_nat(1u);
v_colonTk_23_ = l_Lean_Syntax_getArg(v_x_10_, v___x_22_);
v___x_24_ = l_Lean_Fmt_fmt(v_colonTk_23_, v_a_11_, v_a_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v_a_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_a_25_);
v_a_26_ = lean_ctor_get(v___x_24_, 1);
lean_inc(v_a_26_);
lean_dec_ref_known(v___x_24_, 2);
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = l_Lean_Syntax_getArg(v_x_10_, v___x_27_);
v___x_29_ = l_Lean_Fmt_fmt(v___x_28_, v_a_11_, v_a_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_32_; lean_object* v_rbTk_33_; lean_object* v___x_34_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_a_30_);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
lean_inc(v_a_31_);
lean_dec_ref_known(v___x_29_, 2);
v___x_32_ = lean_unsigned_to_nat(3u);
v_rbTk_33_ = l_Lean_Syntax_getArg(v_x_10_, v___x_32_);
lean_dec(v_x_10_);
v___x_34_ = l_Lean_Fmt_fmt(v_rbTk_33_, v_a_11_, v_a_31_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_50_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_a_36_ = lean_ctor_get(v___x_34_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_50_ == 0)
{
v___x_38_ = v___x_34_;
v_isShared_39_ = v_isSharedCheck_50_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_50_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_40_ = lean_mk_empty_array_with_capacity(v___x_27_);
v___x_41_ = lean_array_push(v___x_40_, v_a_25_);
v___x_42_ = lean_array_push(v___x_41_, v_a_30_);
v___x_43_ = l_Lean_Fmt_Layouts_atomic(v___x_42_);
lean_dec_ref(v___x_42_);
v___x_44_ = 0;
v___x_45_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_45_, 0, v___x_44_);
lean_ctor_set_uint8(v___x_45_, 1, v___x_14_);
v___x_46_ = l_Lean_Fmt_Layouts_bracketed(v_a_20_, v___x_43_, v_a_35_, v___x_45_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v___x_46_);
v___x_48_ = v___x_38_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_a_36_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
else
{
lean_dec(v_a_30_);
lean_dec(v_a_25_);
lean_dec(v_a_20_);
return v___x_34_;
}
}
else
{
lean_dec(v_a_25_);
lean_dec(v_a_20_);
lean_dec(v_x_10_);
return v___x_29_;
}
}
else
{
lean_dec(v_a_20_);
lean_dec(v_x_10_);
return v___x_24_;
}
}
else
{
lean_dec(v_x_10_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBound___boxed(lean_object* v_x_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Fmt_fmtLegacyRangeUpperBound(v_x_51_, v_a_52_, v_a_53_);
lean_dec_ref(v_a_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1(){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_63_ = l_Lean_Fmt_fmtAttribute;
v___x_64_ = ((lean_object*)(l_Lean_Fmt_fmtLegacyRangeUpperBound___closed__4));
v___x_65_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___closed__3));
v___x_66_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLegacyRangeUpperBound___boxed), 3, 0);
v___x_67_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_63_, v___x_64_, v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1___boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeBounds(lean_object* v_x_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Fmt_fmtLegacyRangeBounds___closed__1));
lean_inc(v_x_76_);
v___x_80_ = l_Lean_Syntax_isOfKind(v_x_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_x_76_);
v___x_81_ = l_Lean_Fmt_Error_partialFormatter;
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_78_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v_lbTk_84_; lean_object* v___x_85_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v_lbTk_84_ = l_Lean_Syntax_getArg(v_x_76_, v___x_83_);
v___x_85_ = l_Lean_Fmt_fmt(v_lbTk_84_, v_a_77_, v_a_78_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v_a_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_a_86_);
v_a_87_ = lean_ctor_get(v___x_85_, 1);
lean_inc(v_a_87_);
lean_dec_ref_known(v___x_85_, 2);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = l_Lean_Syntax_getArg(v_x_76_, v___x_88_);
v___x_90_ = l_Lean_Fmt_fmt(v___x_89_, v_a_77_, v_a_87_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_93_; lean_object* v_colonTk_94_; lean_object* v___x_95_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v___x_90_, 1);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_90_, 2);
v___x_93_ = lean_unsigned_to_nat(2u);
v_colonTk_94_ = l_Lean_Syntax_getArg(v_x_76_, v___x_93_);
v___x_95_ = l_Lean_Fmt_fmt(v_colonTk_94_, v_a_77_, v_a_92_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v_a_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
v_a_97_ = lean_ctor_get(v___x_95_, 1);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_95_, 2);
v___x_98_ = lean_unsigned_to_nat(3u);
v___x_99_ = l_Lean_Syntax_getArg(v_x_76_, v___x_98_);
v___x_100_ = l_Lean_Fmt_fmt(v___x_99_, v_a_77_, v_a_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v_rbTk_104_; lean_object* v___x_105_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
v_a_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_100_, 2);
v___x_103_ = lean_unsigned_to_nat(4u);
v_rbTk_104_ = l_Lean_Syntax_getArg(v_x_76_, v___x_103_);
lean_dec(v_x_76_);
v___x_105_ = l_Lean_Fmt_fmt(v_rbTk_104_, v_a_77_, v_a_102_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_123_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_a_107_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_123_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_111_ = lean_mk_empty_array_with_capacity(v___x_98_);
v___x_112_ = lean_array_push(v___x_111_, v_a_91_);
v___x_113_ = lean_array_push(v___x_112_, v_a_96_);
v___x_114_ = lean_array_push(v___x_113_, v_a_101_);
v___x_115_ = 0;
v___x_116_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_116_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_116_, 1, v___x_115_);
lean_ctor_set_uint8(v___x_116_, 2, v___x_115_);
lean_ctor_set_uint8(v___x_116_, 3, v___x_115_);
lean_ctor_set_uint8(v___x_116_, 4, v___x_115_);
v___x_117_ = l_Lean_Fmt_Layouts_infixOperator(v___x_114_, v___x_116_);
lean_dec_ref_known(v___x_116_, 0);
v___x_118_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_118_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_118_, 1, v___x_80_);
v___x_119_ = l_Lean_Fmt_Layouts_bracketed(v_a_86_, v___x_117_, v_a_106_, v___x_118_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_119_);
v___x_121_ = v___x_109_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_a_107_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_dec(v_a_101_);
lean_dec(v_a_96_);
lean_dec(v_a_91_);
lean_dec(v_a_86_);
return v___x_105_;
}
}
else
{
lean_dec(v_a_96_);
lean_dec(v_a_91_);
lean_dec(v_a_86_);
lean_dec(v_x_76_);
return v___x_100_;
}
}
else
{
lean_dec(v_a_91_);
lean_dec(v_a_86_);
lean_dec(v_x_76_);
return v___x_95_;
}
}
else
{
lean_dec(v_a_86_);
lean_dec(v_x_76_);
return v___x_90_;
}
}
else
{
lean_dec(v_x_76_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeBounds___boxed(lean_object* v_x_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Fmt_fmtLegacyRangeBounds(v_x_124_, v_a_125_, v_a_126_);
lean_dec_ref(v_a_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1(){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_134_ = l_Lean_Fmt_fmtAttribute;
v___x_135_ = ((lean_object*)(l_Lean_Fmt_fmtLegacyRangeBounds___closed__1));
v___x_136_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___closed__1));
v___x_137_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLegacyRangeBounds___boxed), 3, 0);
v___x_138_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_134_, v___x_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1___boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1();
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep(lean_object* v_x_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1));
lean_inc(v_x_147_);
v___x_151_ = l_Lean_Syntax_isOfKind(v_x_147_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_x_147_);
v___x_152_ = l_Lean_Fmt_Error_partialFormatter;
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_a_149_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v_lbTk_155_; lean_object* v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v_lbTk_155_ = l_Lean_Syntax_getArg(v_x_147_, v___x_154_);
v___x_156_ = l_Lean_Fmt_fmt(v_lbTk_155_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v_a_158_; lean_object* v___x_159_; lean_object* v_lowerColonTk_160_; lean_object* v___x_161_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
v_a_158_ = lean_ctor_get(v___x_156_, 1);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_156_, 2);
v___x_159_ = lean_unsigned_to_nat(1u);
v_lowerColonTk_160_ = l_Lean_Syntax_getArg(v_x_147_, v___x_159_);
v___x_161_ = l_Lean_Fmt_fmt(v_lowerColonTk_160_, v_a_148_, v_a_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v_a_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
v_a_163_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_161_, 2);
v___x_164_ = lean_unsigned_to_nat(2u);
v___x_165_ = l_Lean_Syntax_getArg(v_x_147_, v___x_164_);
v___x_166_ = l_Lean_Fmt_fmt(v___x_165_, v_a_148_, v_a_163_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v_upperColonTk_170_; lean_object* v___x_171_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
v_a_168_ = lean_ctor_get(v___x_166_, 1);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_166_, 2);
v___x_169_ = lean_unsigned_to_nat(3u);
v_upperColonTk_170_ = l_Lean_Syntax_getArg(v_x_147_, v___x_169_);
v___x_171_ = l_Lean_Fmt_fmt(v_upperColonTk_170_, v_a_148_, v_a_168_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
v_a_173_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_171_, 2);
v___x_174_ = lean_unsigned_to_nat(4u);
v___x_175_ = l_Lean_Syntax_getArg(v_x_147_, v___x_174_);
v___x_176_ = l_Lean_Fmt_fmt(v___x_175_, v_a_148_, v_a_173_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_a_178_; lean_object* v___x_179_; lean_object* v_rbTk_180_; lean_object* v___x_181_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
v_a_178_ = lean_ctor_get(v___x_176_, 1);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_176_, 2);
v___x_179_ = lean_unsigned_to_nat(5u);
v_rbTk_180_ = l_Lean_Syntax_getArg(v_x_147_, v___x_179_);
lean_dec(v_x_147_);
v___x_181_ = l_Lean_Fmt_fmt(v_rbTk_180_, v_a_148_, v_a_178_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_203_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_a_183_ = lean_ctor_get(v___x_181_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_203_ == 0)
{
v___x_185_ = v___x_181_;
v_isShared_186_ = v_isSharedCheck_203_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_203_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_187_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_188_ = lean_array_push(v___x_187_, v_a_167_);
v___x_189_ = lean_array_push(v___x_188_, v_a_172_);
v___x_190_ = lean_array_push(v___x_189_, v_a_177_);
v___x_191_ = 0;
v___x_192_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_192_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_192_, 1, v___x_191_);
lean_ctor_set_uint8(v___x_192_, 2, v___x_191_);
lean_ctor_set_uint8(v___x_192_, 3, v___x_191_);
lean_ctor_set_uint8(v___x_192_, 4, v___x_191_);
v___x_193_ = l_Lean_Fmt_Layouts_infixOperator(v___x_190_, v___x_192_);
lean_dec_ref_known(v___x_192_, 0);
v___x_194_ = lean_mk_empty_array_with_capacity(v___x_164_);
v___x_195_ = lean_array_push(v___x_194_, v_a_162_);
v___x_196_ = lean_array_push(v___x_195_, v___x_193_);
v___x_197_ = l_Lean_Fmt_Layouts_atomic(v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_198_, 0, v___x_191_);
lean_ctor_set_uint8(v___x_198_, 1, v___x_151_);
v___x_199_ = l_Lean_Fmt_Layouts_bracketed(v_a_157_, v___x_197_, v_a_182_, v___x_198_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_199_);
v___x_201_ = v___x_185_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_a_183_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_dec(v_a_177_);
lean_dec(v_a_172_);
lean_dec(v_a_167_);
lean_dec(v_a_162_);
lean_dec(v_a_157_);
return v___x_181_;
}
}
else
{
lean_dec(v_a_172_);
lean_dec(v_a_167_);
lean_dec(v_a_162_);
lean_dec(v_a_157_);
lean_dec(v_x_147_);
return v___x_176_;
}
}
else
{
lean_dec(v_a_167_);
lean_dec(v_a_162_);
lean_dec(v_a_157_);
lean_dec(v_x_147_);
return v___x_171_;
}
}
else
{
lean_dec(v_a_162_);
lean_dec(v_a_157_);
lean_dec(v_x_147_);
return v___x_166_;
}
}
else
{
lean_dec(v_a_157_);
lean_dec(v_x_147_);
return v___x_161_;
}
}
else
{
lean_dec(v_x_147_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___boxed(lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep(v_x_204_, v_a_205_, v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1(){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_214_ = l_Lean_Fmt_fmtAttribute;
v___x_215_ = ((lean_object*)(l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___closed__1));
v___x_216_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___closed__1));
v___x_217_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___boxed), 3, 0);
v___x_218_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_214_, v___x_215_, v___x_216_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1___boxed(lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1();
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeBoundsWithStep(lean_object* v_x_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1));
lean_inc(v_x_227_);
v___x_231_ = l_Lean_Syntax_isOfKind(v_x_227_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_x_227_);
v___x_232_ = l_Lean_Fmt_Error_partialFormatter;
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_a_229_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v_lbTk_235_; lean_object* v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v_lbTk_235_ = l_Lean_Syntax_getArg(v_x_227_, v___x_234_);
v___x_236_ = l_Lean_Fmt_fmt(v_lbTk_235_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v_a_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
v_a_238_ = lean_ctor_get(v___x_236_, 1);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_236_, 2);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = l_Lean_Syntax_getArg(v_x_227_, v___x_239_);
v___x_241_ = l_Lean_Fmt_fmt(v___x_240_, v_a_228_, v_a_238_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v_a_243_; lean_object* v___x_244_; lean_object* v_lowerColonTk_245_; lean_object* v___x_246_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
v_a_243_ = lean_ctor_get(v___x_241_, 1);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_241_, 2);
v___x_244_ = lean_unsigned_to_nat(2u);
v_lowerColonTk_245_ = l_Lean_Syntax_getArg(v_x_227_, v___x_244_);
v___x_246_ = l_Lean_Fmt_fmt(v_lowerColonTk_245_, v_a_228_, v_a_243_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
v_a_248_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_246_, 2);
v___x_249_ = lean_unsigned_to_nat(3u);
v___x_250_ = l_Lean_Syntax_getArg(v_x_227_, v___x_249_);
v___x_251_ = l_Lean_Fmt_fmt(v___x_250_, v_a_228_, v_a_248_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v_a_253_; lean_object* v___x_254_; lean_object* v_upperColonTk_255_; lean_object* v___x_256_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_252_);
v_a_253_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_251_, 2);
v___x_254_ = lean_unsigned_to_nat(4u);
v_upperColonTk_255_ = l_Lean_Syntax_getArg(v_x_227_, v___x_254_);
v___x_256_ = l_Lean_Fmt_fmt(v_upperColonTk_255_, v_a_228_, v_a_253_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v_a_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
v_a_258_ = lean_ctor_get(v___x_256_, 1);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_256_, 2);
v___x_259_ = lean_unsigned_to_nat(5u);
v___x_260_ = l_Lean_Syntax_getArg(v_x_227_, v___x_259_);
v___x_261_ = l_Lean_Fmt_fmt(v___x_260_, v_a_228_, v_a_258_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v_a_263_; lean_object* v___x_264_; lean_object* v_rbTk_265_; lean_object* v___x_266_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
v_a_263_ = lean_ctor_get(v___x_261_, 1);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_261_, 2);
v___x_264_ = lean_unsigned_to_nat(6u);
v_rbTk_265_ = l_Lean_Syntax_getArg(v_x_227_, v___x_264_);
lean_dec(v_x_227_);
v___x_266_ = l_Lean_Fmt_fmt(v_rbTk_265_, v_a_228_, v_a_263_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_286_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_a_268_ = lean_ctor_get(v___x_266_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_286_ == 0)
{
v___x_270_ = v___x_266_;
v_isShared_271_ = v_isSharedCheck_286_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_286_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_272_ = lean_mk_empty_array_with_capacity(v___x_259_);
v___x_273_ = lean_array_push(v___x_272_, v_a_242_);
v___x_274_ = lean_array_push(v___x_273_, v_a_247_);
v___x_275_ = lean_array_push(v___x_274_, v_a_252_);
v___x_276_ = lean_array_push(v___x_275_, v_a_257_);
v___x_277_ = lean_array_push(v___x_276_, v_a_262_);
v___x_278_ = 0;
v___x_279_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_279_, 0, v___x_231_);
lean_ctor_set_uint8(v___x_279_, 1, v___x_278_);
lean_ctor_set_uint8(v___x_279_, 2, v___x_278_);
lean_ctor_set_uint8(v___x_279_, 3, v___x_278_);
lean_ctor_set_uint8(v___x_279_, 4, v___x_278_);
v___x_280_ = l_Lean_Fmt_Layouts_infixOperator(v___x_277_, v___x_279_);
lean_dec_ref_known(v___x_279_, 0);
v___x_281_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_281_, 0, v___x_278_);
lean_ctor_set_uint8(v___x_281_, 1, v___x_231_);
v___x_282_ = l_Lean_Fmt_Layouts_bracketed(v_a_237_, v___x_280_, v_a_267_, v___x_281_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_282_);
v___x_284_ = v___x_270_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_a_268_);
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
lean_dec(v_a_262_);
lean_dec(v_a_257_);
lean_dec(v_a_252_);
lean_dec(v_a_247_);
lean_dec(v_a_242_);
lean_dec(v_a_237_);
return v___x_266_;
}
}
else
{
lean_dec(v_a_257_);
lean_dec(v_a_252_);
lean_dec(v_a_247_);
lean_dec(v_a_242_);
lean_dec(v_a_237_);
lean_dec(v_x_227_);
return v___x_261_;
}
}
else
{
lean_dec(v_a_252_);
lean_dec(v_a_247_);
lean_dec(v_a_242_);
lean_dec(v_a_237_);
lean_dec(v_x_227_);
return v___x_256_;
}
}
else
{
lean_dec(v_a_247_);
lean_dec(v_a_242_);
lean_dec(v_a_237_);
lean_dec(v_x_227_);
return v___x_251_;
}
}
else
{
lean_dec(v_a_242_);
lean_dec(v_a_237_);
lean_dec(v_x_227_);
return v___x_246_;
}
}
else
{
lean_dec(v_a_237_);
lean_dec(v_x_227_);
return v___x_241_;
}
}
else
{
lean_dec(v_x_227_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___boxed(lean_object* v_x_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Fmt_fmtLegacyRangeBoundsWithStep(v_x_287_, v_a_288_, v_a_289_);
lean_dec_ref(v_a_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1(){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_297_ = l_Lean_Fmt_fmtAttribute;
v___x_298_ = ((lean_object*)(l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___closed__1));
v___x_299_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___closed__1));
v___x_300_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLegacyRangeBoundsWithStep___boxed), 3, 0);
v___x_301_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_297_, v___x_298_, v___x_299_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1___boxed(lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1();
return v_res_303_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data_Range_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBound___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBound__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBounds___regBuiltin_Lean_Fmt_fmtLegacyRangeBounds__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeUpperBoundWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeUpperBoundWithStep__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Basic_0__Lean_Fmt_fmtLegacyRangeBoundsWithStep___regBuiltin_Lean_Fmt_fmtLegacyRangeBoundsWithStep__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_Range_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Data_Range_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Range_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Data_Range_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data_Range_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Data_Range_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Data_Range_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
