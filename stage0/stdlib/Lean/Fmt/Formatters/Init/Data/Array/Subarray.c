// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Data.Array.Subarray
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Data.Array.Subarray import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtSubarraySlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtSubarraySlice___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSubarraySlice___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarraySlice(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSubarrayBounds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Fmt_fmtSubarrayBounds___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSubarrayBounds___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSubarrayBounds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_:_]"};
static const lean_object* l_Lean_Fmt_fmtSubarrayBounds___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSubarrayBounds___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtSubarrayBounds___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSubarrayBounds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Fmt_fmtSubarrayBounds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSubarrayBounds___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSubarrayBounds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(25, 16, 196, 182, 60, 93, 13, 211)}};
static const lean_object* l_Lean_Fmt_fmtSubarrayBounds___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSubarrayBounds___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayBounds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayBounds___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtSubarrayBounds"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 82, 194, 17, 106, 128, 221, 84)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSubarrayLowerBound___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term__[_:]"};
static const lean_object* l_Lean_Fmt_fmtSubarrayLowerBound___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSubarrayLowerBound___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSubarrayLowerBound___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSubarrayBounds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Fmt_fmtSubarrayLowerBound___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSubarrayLowerBound___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSubarrayLowerBound___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 86, 15, 94, 195, 189, 15, 195)}};
static const lean_object* l_Lean_Fmt_fmtSubarrayLowerBound___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSubarrayLowerBound___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayLowerBound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayLowerBound___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtSubarrayLowerBound"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 50, 26, 85, 16, 233, 98, 198)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSubarrayUpperBound___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term__[:_]"};
static const lean_object* l_Lean_Fmt_fmtSubarrayUpperBound___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSubarrayUpperBound___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSubarrayUpperBound___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSubarrayBounds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Fmt_fmtSubarrayUpperBound___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSubarrayUpperBound___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSubarrayUpperBound___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 75, 86, 255, 23, 9, 108, 116)}};
static const lean_object* l_Lean_Fmt_fmtSubarrayUpperBound___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSubarrayUpperBound___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayUpperBound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayUpperBound___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtSubarrayUpperBound"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 2, 147, 133, 111, 37, 173, 176)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarraySlice(lean_object* v_a_4_, lean_object* v_lbTk_5_, lean_object* v_bounds_6_, lean_object* v_rbTk_7_){
_start:
{
uint8_t v___x_8_; lean_object* v___x_9_; lean_object* v_slice_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_8_ = 0;
v___x_9_ = ((lean_object*)(l_Lean_Fmt_fmtSubarraySlice___closed__0));
v_slice_10_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_5_, v_bounds_6_, v_rbTk_7_, v___x_9_);
v___x_11_ = lean_unsigned_to_nat(2u);
v___x_12_ = lean_mk_empty_array_with_capacity(v___x_11_);
v___x_13_ = lean_array_push(v___x_12_, v_a_4_);
v___x_14_ = lean_array_push(v___x_13_, v_slice_10_);
v___x_15_ = l_Lean_Fmt_Layouts_atomic(v___x_14_);
lean_dec_ref(v___x_14_);
v___x_16_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_15_, v___x_8_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayBounds(lean_object* v_x_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = ((lean_object*)(l_Lean_Fmt_fmtSubarrayBounds___closed__2));
lean_inc(v_x_22_);
v___x_26_ = l_Lean_Syntax_isOfKind(v_x_22_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v_x_22_);
v___x_27_ = l_Lean_Fmt_Error_partialFormatter;
v___x_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v_a_24_);
return v___x_28_;
}
else
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = l_Lean_Syntax_getArg(v_x_22_, v___x_29_);
v___x_31_ = l_Lean_Fmt_fmt(v___x_30_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v_a_33_; lean_object* v___x_34_; lean_object* v_lbTk_35_; lean_object* v___x_36_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_a_32_);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
lean_inc(v_a_33_);
lean_dec_ref_known(v___x_31_, 2);
v___x_34_ = lean_unsigned_to_nat(1u);
v_lbTk_35_ = l_Lean_Syntax_getArg(v_x_22_, v___x_34_);
v___x_36_ = l_Lean_Fmt_fmt(v_lbTk_35_, v_a_23_, v_a_33_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v_a_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_37_);
v_a_38_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_a_38_);
lean_dec_ref_known(v___x_36_, 2);
v___x_39_ = lean_unsigned_to_nat(2u);
v___x_40_ = l_Lean_Syntax_getArg(v_x_22_, v___x_39_);
v___x_41_ = l_Lean_Fmt_fmt(v___x_40_, v_a_23_, v_a_38_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v_a_43_; lean_object* v___x_44_; lean_object* v_colonTk_45_; lean_object* v___x_46_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_a_42_);
v_a_43_ = lean_ctor_get(v___x_41_, 1);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_41_, 2);
v___x_44_ = lean_unsigned_to_nat(3u);
v_colonTk_45_ = l_Lean_Syntax_getArg(v_x_22_, v___x_44_);
v___x_46_ = l_Lean_Fmt_fmt(v_colonTk_45_, v_a_23_, v_a_43_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v_a_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
v_a_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_46_, 2);
v___x_49_ = lean_unsigned_to_nat(4u);
v___x_50_ = l_Lean_Syntax_getArg(v_x_22_, v___x_49_);
v___x_51_ = l_Lean_Fmt_fmt(v___x_50_, v_a_23_, v_a_48_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v_a_53_; lean_object* v___x_54_; lean_object* v_rbTk_55_; lean_object* v___x_56_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
v_a_53_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_a_53_);
lean_dec_ref_known(v___x_51_, 2);
v___x_54_ = lean_unsigned_to_nat(5u);
v_rbTk_55_ = l_Lean_Syntax_getArg(v_x_22_, v___x_54_);
lean_dec(v_x_22_);
v___x_56_ = l_Lean_Fmt_fmt(v_rbTk_55_, v_a_23_, v_a_53_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_73_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_a_58_ = lean_ctor_get(v___x_56_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_73_ == 0)
{
v___x_60_ = v___x_56_;
v_isShared_61_ = v_isSharedCheck_73_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_73_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_62_ = lean_mk_empty_array_with_capacity(v___x_44_);
v___x_63_ = lean_array_push(v___x_62_, v_a_42_);
v___x_64_ = lean_array_push(v___x_63_, v_a_47_);
v___x_65_ = lean_array_push(v___x_64_, v_a_52_);
v___x_66_ = 0;
v___x_67_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_67_, 0, v___x_26_);
lean_ctor_set_uint8(v___x_67_, 1, v___x_66_);
lean_ctor_set_uint8(v___x_67_, 2, v___x_66_);
lean_ctor_set_uint8(v___x_67_, 3, v___x_66_);
lean_ctor_set_uint8(v___x_67_, 4, v___x_66_);
v___x_68_ = l_Lean_Fmt_Layouts_infixOperator(v___x_65_, v___x_67_);
lean_dec_ref_known(v___x_67_, 0);
v___x_69_ = l_Lean_Fmt_fmtSubarraySlice(v_a_32_, v_a_37_, v___x_68_, v_a_57_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_69_);
v___x_71_ = v___x_60_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_a_58_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
else
{
lean_dec(v_a_52_);
lean_dec(v_a_47_);
lean_dec(v_a_42_);
lean_dec(v_a_37_);
lean_dec(v_a_32_);
return v___x_56_;
}
}
else
{
lean_dec(v_a_47_);
lean_dec(v_a_42_);
lean_dec(v_a_37_);
lean_dec(v_a_32_);
lean_dec(v_x_22_);
return v___x_51_;
}
}
else
{
lean_dec(v_a_42_);
lean_dec(v_a_37_);
lean_dec(v_a_32_);
lean_dec(v_x_22_);
return v___x_46_;
}
}
else
{
lean_dec(v_a_37_);
lean_dec(v_a_32_);
lean_dec(v_x_22_);
return v___x_41_;
}
}
else
{
lean_dec(v_a_32_);
lean_dec(v_x_22_);
return v___x_36_;
}
}
else
{
lean_dec(v_x_22_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayBounds___boxed(lean_object* v_x_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Fmt_fmtSubarrayBounds(v_x_74_, v_a_75_, v_a_76_);
lean_dec_ref(v_a_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1(){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = l_Lean_Fmt_fmtAttribute;
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtSubarrayBounds___closed__2));
v___x_88_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___closed__3));
v___x_89_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSubarrayBounds___boxed), 3, 0);
v___x_90_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_86_, v___x_87_, v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1___boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayLowerBound(lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Fmt_fmtSubarrayLowerBound___closed__1));
lean_inc(v_x_97_);
v___x_101_ = l_Lean_Syntax_isOfKind(v_x_97_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v_x_97_);
v___x_102_ = l_Lean_Fmt_Error_partialFormatter;
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_a_99_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_97_, v___x_104_);
v___x_106_ = l_Lean_Fmt_fmt(v___x_105_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v_lbTk_110_; lean_object* v___x_111_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
v_a_108_ = lean_ctor_get(v___x_106_, 1);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_106_, 2);
v___x_109_ = lean_unsigned_to_nat(1u);
v_lbTk_110_ = l_Lean_Syntax_getArg(v_x_97_, v___x_109_);
v___x_111_ = l_Lean_Fmt_fmt(v_lbTk_110_, v_a_98_, v_a_108_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v_a_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
v_a_113_ = lean_ctor_get(v___x_111_, 1);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_111_, 2);
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_97_, v___x_114_);
v___x_116_ = l_Lean_Fmt_fmt(v___x_115_, v_a_98_, v_a_113_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v_a_118_; lean_object* v___x_119_; lean_object* v_colonTk_120_; lean_object* v___x_121_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
v_a_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_116_, 2);
v___x_119_ = lean_unsigned_to_nat(3u);
v_colonTk_120_ = l_Lean_Syntax_getArg(v_x_97_, v___x_119_);
v___x_121_ = l_Lean_Fmt_fmt(v_colonTk_120_, v_a_98_, v_a_118_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v_a_123_; lean_object* v___x_124_; lean_object* v_rbTk_125_; lean_object* v___x_126_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
v_a_123_ = lean_ctor_get(v___x_121_, 1);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_121_, 2);
v___x_124_ = lean_unsigned_to_nat(4u);
v_rbTk_125_ = l_Lean_Syntax_getArg(v_x_97_, v___x_124_);
lean_dec(v_x_97_);
v___x_126_ = l_Lean_Fmt_fmt(v_rbTk_125_, v_a_98_, v_a_123_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_140_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_a_128_ = lean_ctor_get(v___x_126_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_140_ == 0)
{
v___x_130_ = v___x_126_;
v_isShared_131_ = v_isSharedCheck_140_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_140_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_132_ = lean_mk_empty_array_with_capacity(v___x_114_);
v___x_133_ = lean_array_push(v___x_132_, v_a_117_);
v___x_134_ = lean_array_push(v___x_133_, v_a_122_);
v___x_135_ = l_Lean_Fmt_Layouts_atomic(v___x_134_);
lean_dec_ref(v___x_134_);
v___x_136_ = l_Lean_Fmt_fmtSubarraySlice(v_a_107_, v_a_112_, v___x_135_, v_a_127_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_136_);
v___x_138_ = v___x_130_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_a_128_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
lean_dec(v_a_122_);
lean_dec(v_a_117_);
lean_dec(v_a_112_);
lean_dec(v_a_107_);
return v___x_126_;
}
}
else
{
lean_dec(v_a_117_);
lean_dec(v_a_112_);
lean_dec(v_a_107_);
lean_dec(v_x_97_);
return v___x_121_;
}
}
else
{
lean_dec(v_a_112_);
lean_dec(v_a_107_);
lean_dec(v_x_97_);
return v___x_116_;
}
}
else
{
lean_dec(v_a_107_);
lean_dec(v_x_97_);
return v___x_111_;
}
}
else
{
lean_dec(v_x_97_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayLowerBound___boxed(lean_object* v_x_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Fmt_fmtSubarrayLowerBound(v_x_141_, v_a_142_, v_a_143_);
lean_dec_ref(v_a_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1(){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = l_Lean_Fmt_fmtAttribute;
v___x_152_ = ((lean_object*)(l_Lean_Fmt_fmtSubarrayLowerBound___closed__1));
v___x_153_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___closed__1));
v___x_154_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSubarrayLowerBound___boxed), 3, 0);
v___x_155_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_151_, v___x_152_, v___x_153_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1___boxed(lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1();
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayUpperBound(lean_object* v_x_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Fmt_fmtSubarrayUpperBound___closed__1));
lean_inc(v_x_162_);
v___x_166_ = l_Lean_Syntax_isOfKind(v_x_162_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_x_162_);
v___x_167_ = l_Lean_Fmt_Error_partialFormatter;
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v_a_164_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = l_Lean_Syntax_getArg(v_x_162_, v___x_169_);
v___x_171_ = l_Lean_Fmt_fmt(v___x_170_, v_a_163_, v_a_164_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v_lbTk_175_; lean_object* v___x_176_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
v_a_173_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_171_, 2);
v___x_174_ = lean_unsigned_to_nat(1u);
v_lbTk_175_ = l_Lean_Syntax_getArg(v_x_162_, v___x_174_);
v___x_176_ = l_Lean_Fmt_fmt(v_lbTk_175_, v_a_163_, v_a_173_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_a_178_; lean_object* v___x_179_; lean_object* v_colonTk_180_; lean_object* v___x_181_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
v_a_178_ = lean_ctor_get(v___x_176_, 1);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_176_, 2);
v___x_179_ = lean_unsigned_to_nat(2u);
v_colonTk_180_ = l_Lean_Syntax_getArg(v_x_162_, v___x_179_);
v___x_181_ = l_Lean_Fmt_fmt(v_colonTk_180_, v_a_163_, v_a_178_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v_a_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
v_a_183_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_181_, 2);
v___x_184_ = lean_unsigned_to_nat(3u);
v___x_185_ = l_Lean_Syntax_getArg(v_x_162_, v___x_184_);
v___x_186_ = l_Lean_Fmt_fmt(v___x_185_, v_a_163_, v_a_183_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v_a_188_; lean_object* v___x_189_; lean_object* v_rbTk_190_; lean_object* v___x_191_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
v_a_188_ = lean_ctor_get(v___x_186_, 1);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_186_, 2);
v___x_189_ = lean_unsigned_to_nat(4u);
v_rbTk_190_ = l_Lean_Syntax_getArg(v_x_162_, v___x_189_);
lean_dec(v_x_162_);
v___x_191_ = l_Lean_Fmt_fmt(v_rbTk_190_, v_a_163_, v_a_188_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_205_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_a_193_ = lean_ctor_get(v___x_191_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_205_ == 0)
{
v___x_195_ = v___x_191_;
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_197_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_198_ = lean_array_push(v___x_197_, v_a_182_);
v___x_199_ = lean_array_push(v___x_198_, v_a_187_);
v___x_200_ = l_Lean_Fmt_Layouts_atomic(v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_Lean_Fmt_fmtSubarraySlice(v_a_172_, v_a_177_, v___x_200_, v_a_192_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_201_);
v___x_203_ = v___x_195_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_a_193_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_dec(v_a_187_);
lean_dec(v_a_182_);
lean_dec(v_a_177_);
lean_dec(v_a_172_);
return v___x_191_;
}
}
else
{
lean_dec(v_a_182_);
lean_dec(v_a_177_);
lean_dec(v_a_172_);
lean_dec(v_x_162_);
return v___x_186_;
}
}
else
{
lean_dec(v_a_177_);
lean_dec(v_a_172_);
lean_dec(v_x_162_);
return v___x_181_;
}
}
else
{
lean_dec(v_a_172_);
lean_dec(v_x_162_);
return v___x_176_;
}
}
else
{
lean_dec(v_x_162_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubarrayUpperBound___boxed(lean_object* v_x_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Fmt_fmtSubarrayUpperBound(v_x_206_, v_a_207_, v_a_208_);
lean_dec_ref(v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1(){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_216_ = l_Lean_Fmt_fmtAttribute;
v___x_217_ = ((lean_object*)(l_Lean_Fmt_fmtSubarrayUpperBound___closed__1));
v___x_218_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___closed__1));
v___x_219_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSubarrayUpperBound___boxed), 3, 0);
v___x_220_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_216_, v___x_217_, v___x_218_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1___boxed(lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1();
return v_res_222_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data_Array_Subarray(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayBounds___regBuiltin_Lean_Fmt_fmtSubarrayBounds__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayLowerBound___regBuiltin_Lean_Fmt_fmtSubarrayLowerBound__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Array_Subarray_0__Lean_Fmt_fmtSubarrayUpperBound___regBuiltin_Lean_Fmt_fmtSubarrayUpperBound__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Data_Array_Subarray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Data_Array_Subarray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Data_Array_Subarray(builtin);
}
#ifdef __cplusplus
}
#endif
