// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Data.Range.Polymorphic.PRange
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Data.Range.Polymorphic.PRange import Init.Data
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
lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
static const lean_ctor_object l_Lean_Fmt_fmtRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtRange___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRange___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRco___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtRangeRco___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRangeRco___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_..._"};
static const lean_object* l_Lean_Fmt_fmtRangeRco___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRco___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRco___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 215, 136, 196, 225, 228, 219, 74)}};
static const lean_object* l_Lean_Fmt_fmtRangeRco___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRco(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRco___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtRangeRco"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 70, 42, 108, 181, 164, 1, 168)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRcoExcl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_...<_"};
static const lean_object* l_Lean_Fmt_fmtRangeRcoExcl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRcoExcl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRcoExcl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRcoExcl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRcoExcl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRcoExcl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 56, 180, 150, 42, 67, 215, 61)}};
static const lean_object* l_Lean_Fmt_fmtRangeRcoExcl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRcoExcl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRcoExcl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRcoExcl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtRangeRcoExcl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 184, 74, 64, 1, 237, 56, 60)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRcc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_...=_"};
static const lean_object* l_Lean_Fmt_fmtRangeRcc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRcc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRcc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRcc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRcc___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRcc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 81, 4, 194, 158, 170, 93, 115)}};
static const lean_object* l_Lean_Fmt_fmtRangeRcc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRcc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRcc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRcc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtRangeRcc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 150, 34, 226, 58, 231, 33, 59)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRoo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_<..._"};
static const lean_object* l_Lean_Fmt_fmtRangeRoo___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRoo___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRoo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRoo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRoo___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRoo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 200, 25, 103, 90, 101, 53, 48)}};
static const lean_object* l_Lean_Fmt_fmtRangeRoo___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRoo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtRangeRoo"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 75, 95, 184, 169, 91, 84, 68)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRooExcl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term_<...<_"};
static const lean_object* l_Lean_Fmt_fmtRangeRooExcl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRooExcl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRooExcl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRooExcl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRooExcl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRooExcl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 24, 184, 113, 209, 224, 82, 248)}};
static const lean_object* l_Lean_Fmt_fmtRangeRooExcl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRooExcl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRooExcl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRooExcl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtRangeRooExcl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 248, 235, 156, 144, 180, 20, 130)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRoc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term_<...=_"};
static const lean_object* l_Lean_Fmt_fmtRangeRoc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRoc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRoc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRoc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRoc___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRoc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 72, 254, 139, 229, 96, 28, 211)}};
static const lean_object* l_Lean_Fmt_fmtRangeRoc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRoc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtRangeRoc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 37, 165, 167, 62, 102, 217, 13)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term*..._"};
static const lean_object* l_Lean_Fmt_fmtRangeRio___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRio___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRio___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRio___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRio___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRio___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 214, 10, 96, 112, 57, 139, 148)}};
static const lean_object* l_Lean_Fmt_fmtRangeRio___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRio___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRio___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtRangeRio"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 186, 49, 218, 208, 102, 118, 10)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRioExcl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term*...<_"};
static const lean_object* l_Lean_Fmt_fmtRangeRioExcl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRioExcl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRioExcl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRioExcl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRioExcl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRioExcl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 95, 249, 207, 5, 93, 41, 245)}};
static const lean_object* l_Lean_Fmt_fmtRangeRioExcl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRioExcl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRioExcl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRioExcl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtRangeRioExcl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 35, 249, 20, 255, 207, 69, 43)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term*...=_"};
static const lean_object* l_Lean_Fmt_fmtRangeRic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 142, 110, 52, 44, 186, 117, 12)}};
static const lean_object* l_Lean_Fmt_fmtRangeRic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtRangeRic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 11, 186, 234, 138, 55, 173, 81)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRci___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_...*"};
static const lean_object* l_Lean_Fmt_fmtRangeRci___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRci___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRci___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRci___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRci___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRci___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 184, 85, 23, 243, 11, 13, 179)}};
static const lean_object* l_Lean_Fmt_fmtRangeRci___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRci___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRci(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRci___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtRangeRci"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 20, 72, 65, 44, 204, 46, 73)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRangeRoi___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_<...*"};
static const lean_object* l_Lean_Fmt_fmtRangeRoi___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRangeRoi___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRangeRoi___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRangeRco___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtRangeRoi___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRangeRoi___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRangeRoi___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 27, 224, 193, 208, 224, 37, 254)}};
static const lean_object* l_Lean_Fmt_fmtRangeRoi___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRangeRoi___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoi(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoi___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtRangeRoi"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 54, 77, 187, 170, 187, 119, 121)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRange(lean_object* v_lhs_4_, lean_object* v_op_5_, lean_object* v_rhs_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Fmt_fmt(v_lhs_4_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
v_a_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_a_11_);
lean_dec_ref_known(v___x_9_, 2);
v___x_12_ = l_Lean_Fmt_fmt(v_op_5_, v_a_7_, v_a_11_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
v_a_14_ = lean_ctor_get(v___x_12_, 1);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_12_, 2);
v___x_15_ = l_Lean_Fmt_fmt(v_rhs_6_, v_a_7_, v_a_14_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_33_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
v_a_17_ = lean_ctor_get(v___x_15_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_33_ == 0)
{
v___x_19_ = v___x_15_;
v_isShared_20_ = v_isSharedCheck_33_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_inc(v_a_16_);
lean_dec(v___x_15_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_33_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_21_ = lean_unsigned_to_nat(3u);
v___x_22_ = lean_mk_empty_array_with_capacity(v___x_21_);
v___x_23_ = lean_array_push(v___x_22_, v_a_10_);
v___x_24_ = lean_array_push(v___x_23_, v_a_13_);
v___x_25_ = lean_array_push(v___x_24_, v_a_16_);
v___x_26_ = 0;
v___x_27_ = ((lean_object*)(l_Lean_Fmt_fmtRange___closed__0));
v___x_28_ = l_Lean_Fmt_Layouts_infixOperator(v___x_25_, v___x_27_);
v___x_29_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_28_, v___x_26_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_29_);
v___x_31_ = v___x_19_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_a_17_);
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
lean_dec(v_a_13_);
lean_dec(v_a_10_);
return v___x_15_;
}
}
else
{
lean_dec(v_a_10_);
lean_dec(v_rhs_6_);
return v___x_12_;
}
}
else
{
lean_dec(v_rhs_6_);
lean_dec(v_op_5_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRange___boxed(lean_object* v_lhs_34_, lean_object* v_op_35_, lean_object* v_rhs_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Fmt_fmtRange(v_lhs_34_, v_op_35_, v_rhs_36_, v_a_37_, v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixRange(lean_object* v_op_40_, lean_object* v_rhs_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Fmt_fmt(v_op_40_, v_a_42_, v_a_43_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v_a_46_; lean_object* v___x_47_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
v_a_46_ = lean_ctor_get(v___x_44_, 1);
lean_inc(v_a_46_);
lean_dec_ref_known(v___x_44_, 2);
v___x_47_ = l_Lean_Fmt_fmt(v_rhs_41_, v_a_42_, v_a_46_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_60_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_a_49_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_60_ == 0)
{
v___x_51_ = v___x_47_;
v_isShared_52_ = v_isSharedCheck_60_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_60_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint8_t v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_53_ = 0;
v___x_54_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_45_, v_a_48_, v___x_53_);
v___x_55_ = 0;
v___x_56_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_54_, v___x_55_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_56_);
v___x_58_ = v___x_51_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_a_49_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
else
{
lean_dec(v_a_45_);
return v___x_47_;
}
}
else
{
lean_dec(v_rhs_41_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixRange___boxed(lean_object* v_op_61_, lean_object* v_rhs_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Fmt_fmtPrefixRange(v_op_61_, v_rhs_62_, v_a_63_, v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixRange(lean_object* v_lhs_66_, lean_object* v_op_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Fmt_fmt(v_lhs_66_, v_a_68_, v_a_69_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v_a_72_; lean_object* v___x_73_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
v_a_72_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_70_, 2);
v___x_73_ = l_Lean_Fmt_fmt(v_op_67_, v_a_68_, v_a_72_);
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
uint8_t v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_79_ = 0;
v___x_80_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_71_, v_a_74_, v___x_79_);
v___x_81_ = 0;
v___x_82_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_80_, v___x_81_);
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
lean_dec(v_a_71_);
return v___x_73_;
}
}
else
{
lean_dec(v_op_67_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixRange___boxed(lean_object* v_lhs_87_, lean_object* v_op_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Fmt_fmtPostfixRange(v_lhs_87_, v_op_88_, v_a_89_, v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRco(lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRco___closed__2));
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
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_opTk_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_97_, v___x_104_);
v___x_106_ = lean_unsigned_to_nat(1u);
v_opTk_107_ = l_Lean_Syntax_getArg(v_x_97_, v___x_106_);
v___x_108_ = lean_unsigned_to_nat(2u);
v___x_109_ = l_Lean_Syntax_getArg(v_x_97_, v___x_108_);
lean_dec(v_x_97_);
v___x_110_ = l_Lean_Fmt_fmtRange(v___x_105_, v_opTk_107_, v___x_109_, v_a_98_, v_a_99_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRco___boxed(lean_object* v_x_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Fmt_fmtRangeRco(v_x_111_, v_a_112_, v_a_113_);
lean_dec_ref(v_a_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1(){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_123_ = l_Lean_Fmt_fmtAttribute;
v___x_124_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRco___closed__2));
v___x_125_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___closed__3));
v___x_126_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRco___boxed), 3, 0);
v___x_127_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_123_, v___x_124_, v___x_125_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1___boxed(lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1();
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRcoExcl(lean_object* v_x_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRcoExcl___closed__1));
lean_inc(v_x_134_);
v___x_138_ = l_Lean_Syntax_isOfKind(v_x_134_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_x_134_);
v___x_139_ = l_Lean_Fmt_Error_partialFormatter;
v___x_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_a_136_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_opTk_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = l_Lean_Syntax_getArg(v_x_134_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(1u);
v_opTk_144_ = l_Lean_Syntax_getArg(v_x_134_, v___x_143_);
v___x_145_ = lean_unsigned_to_nat(2u);
v___x_146_ = l_Lean_Syntax_getArg(v_x_134_, v___x_145_);
lean_dec(v_x_134_);
v___x_147_ = l_Lean_Fmt_fmtRange(v___x_142_, v_opTk_144_, v___x_146_, v_a_135_, v_a_136_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRcoExcl___boxed(lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Fmt_fmtRangeRcoExcl(v_x_148_, v_a_149_, v_a_150_);
lean_dec_ref(v_a_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1(){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_158_ = l_Lean_Fmt_fmtAttribute;
v___x_159_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRcoExcl___closed__1));
v___x_160_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___closed__1));
v___x_161_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRcoExcl___boxed), 3, 0);
v___x_162_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_158_, v___x_159_, v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1___boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1();
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRcc(lean_object* v_x_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRcc___closed__1));
lean_inc(v_x_169_);
v___x_173_ = l_Lean_Syntax_isOfKind(v_x_169_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_x_169_);
v___x_174_ = l_Lean_Fmt_Error_partialFormatter;
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_a_171_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_opTk_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = l_Lean_Syntax_getArg(v_x_169_, v___x_176_);
v___x_178_ = lean_unsigned_to_nat(1u);
v_opTk_179_ = l_Lean_Syntax_getArg(v_x_169_, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(2u);
v___x_181_ = l_Lean_Syntax_getArg(v_x_169_, v___x_180_);
lean_dec(v_x_169_);
v___x_182_ = l_Lean_Fmt_fmtRange(v___x_177_, v_opTk_179_, v___x_181_, v_a_170_, v_a_171_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRcc___boxed(lean_object* v_x_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Fmt_fmtRangeRcc(v_x_183_, v_a_184_, v_a_185_);
lean_dec_ref(v_a_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1(){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_193_ = l_Lean_Fmt_fmtAttribute;
v___x_194_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRcc___closed__1));
v___x_195_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___closed__1));
v___x_196_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRcc___boxed), 3, 0);
v___x_197_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_193_, v___x_194_, v___x_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1___boxed(lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1();
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoo(lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRoo___closed__1));
lean_inc(v_x_204_);
v___x_208_ = l_Lean_Syntax_isOfKind(v_x_204_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_x_204_);
v___x_209_ = l_Lean_Fmt_Error_partialFormatter;
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_a_206_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_opTk_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = l_Lean_Syntax_getArg(v_x_204_, v___x_211_);
v___x_213_ = lean_unsigned_to_nat(1u);
v_opTk_214_ = l_Lean_Syntax_getArg(v_x_204_, v___x_213_);
v___x_215_ = lean_unsigned_to_nat(2u);
v___x_216_ = l_Lean_Syntax_getArg(v_x_204_, v___x_215_);
lean_dec(v_x_204_);
v___x_217_ = l_Lean_Fmt_fmtRange(v___x_212_, v_opTk_214_, v___x_216_, v_a_205_, v_a_206_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoo___boxed(lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Fmt_fmtRangeRoo(v_x_218_, v_a_219_, v_a_220_);
lean_dec_ref(v_a_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1(){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_228_ = l_Lean_Fmt_fmtAttribute;
v___x_229_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRoo___closed__1));
v___x_230_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___closed__1));
v___x_231_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRoo___boxed), 3, 0);
v___x_232_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_228_, v___x_229_, v___x_230_, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1___boxed(lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1();
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRooExcl(lean_object* v_x_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRooExcl___closed__1));
lean_inc(v_x_239_);
v___x_243_ = l_Lean_Syntax_isOfKind(v_x_239_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_x_239_);
v___x_244_ = l_Lean_Fmt_Error_partialFormatter;
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_a_241_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_opTk_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = l_Lean_Syntax_getArg(v_x_239_, v___x_246_);
v___x_248_ = lean_unsigned_to_nat(1u);
v_opTk_249_ = l_Lean_Syntax_getArg(v_x_239_, v___x_248_);
v___x_250_ = lean_unsigned_to_nat(2u);
v___x_251_ = l_Lean_Syntax_getArg(v_x_239_, v___x_250_);
lean_dec(v_x_239_);
v___x_252_ = l_Lean_Fmt_fmtRange(v___x_247_, v_opTk_249_, v___x_251_, v_a_240_, v_a_241_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRooExcl___boxed(lean_object* v_x_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Fmt_fmtRangeRooExcl(v_x_253_, v_a_254_, v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1(){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = l_Lean_Fmt_fmtAttribute;
v___x_264_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRooExcl___closed__1));
v___x_265_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___closed__1));
v___x_266_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRooExcl___boxed), 3, 0);
v___x_267_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_263_, v___x_264_, v___x_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1___boxed(lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoc(lean_object* v_x_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRoc___closed__1));
lean_inc(v_x_274_);
v___x_278_ = l_Lean_Syntax_isOfKind(v_x_274_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v_x_274_);
v___x_279_ = l_Lean_Fmt_Error_partialFormatter;
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_a_276_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_opTk_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Lean_Syntax_getArg(v_x_274_, v___x_281_);
v___x_283_ = lean_unsigned_to_nat(1u);
v_opTk_284_ = l_Lean_Syntax_getArg(v_x_274_, v___x_283_);
v___x_285_ = lean_unsigned_to_nat(2u);
v___x_286_ = l_Lean_Syntax_getArg(v_x_274_, v___x_285_);
lean_dec(v_x_274_);
v___x_287_ = l_Lean_Fmt_fmtRange(v___x_282_, v_opTk_284_, v___x_286_, v_a_275_, v_a_276_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoc___boxed(lean_object* v_x_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Fmt_fmtRangeRoc(v_x_288_, v_a_289_, v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1(){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_298_ = l_Lean_Fmt_fmtAttribute;
v___x_299_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRoc___closed__1));
v___x_300_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___closed__1));
v___x_301_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRoc___boxed), 3, 0);
v___x_302_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_298_, v___x_299_, v___x_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1___boxed(lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRio(lean_object* v_x_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRio___closed__1));
lean_inc(v_x_309_);
v___x_313_ = l_Lean_Syntax_isOfKind(v_x_309_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_x_309_);
v___x_314_ = l_Lean_Fmt_Error_partialFormatter;
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_a_311_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v_opTk_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v_opTk_317_ = l_Lean_Syntax_getArg(v_x_309_, v___x_316_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = l_Lean_Syntax_getArg(v_x_309_, v___x_318_);
lean_dec(v_x_309_);
v___x_320_ = l_Lean_Fmt_fmtPrefixRange(v_opTk_317_, v___x_319_, v_a_310_, v_a_311_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRio___boxed(lean_object* v_x_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Fmt_fmtRangeRio(v_x_321_, v_a_322_, v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1(){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = l_Lean_Fmt_fmtAttribute;
v___x_332_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRio___closed__1));
v___x_333_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___closed__1));
v___x_334_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRio___boxed), 3, 0);
v___x_335_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_331_, v___x_332_, v___x_333_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1___boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRioExcl(lean_object* v_x_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRioExcl___closed__1));
lean_inc(v_x_342_);
v___x_346_ = l_Lean_Syntax_isOfKind(v_x_342_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_x_342_);
v___x_347_ = l_Lean_Fmt_Error_partialFormatter;
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_a_344_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v_opTk_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v_opTk_350_ = l_Lean_Syntax_getArg(v_x_342_, v___x_349_);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = l_Lean_Syntax_getArg(v_x_342_, v___x_351_);
lean_dec(v_x_342_);
v___x_353_ = l_Lean_Fmt_fmtPrefixRange(v_opTk_350_, v___x_352_, v_a_343_, v_a_344_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRioExcl___boxed(lean_object* v_x_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Fmt_fmtRangeRioExcl(v_x_354_, v_a_355_, v_a_356_);
lean_dec_ref(v_a_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1(){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_364_ = l_Lean_Fmt_fmtAttribute;
v___x_365_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRioExcl___closed__1));
v___x_366_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___closed__1));
v___x_367_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRioExcl___boxed), 3, 0);
v___x_368_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_364_, v___x_365_, v___x_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1___boxed(lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1();
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRic(lean_object* v_x_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRic___closed__1));
lean_inc(v_x_375_);
v___x_379_ = l_Lean_Syntax_isOfKind(v_x_375_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_x_375_);
v___x_380_ = l_Lean_Fmt_Error_partialFormatter;
v___x_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_a_377_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; lean_object* v_opTk_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v_opTk_383_ = l_Lean_Syntax_getArg(v_x_375_, v___x_382_);
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = l_Lean_Syntax_getArg(v_x_375_, v___x_384_);
lean_dec(v_x_375_);
v___x_386_ = l_Lean_Fmt_fmtPrefixRange(v_opTk_383_, v___x_385_, v_a_376_, v_a_377_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRic___boxed(lean_object* v_x_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Fmt_fmtRangeRic(v_x_387_, v_a_388_, v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1(){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_397_ = l_Lean_Fmt_fmtAttribute;
v___x_398_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRic___closed__1));
v___x_399_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___closed__1));
v___x_400_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRic___boxed), 3, 0);
v___x_401_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_397_, v___x_398_, v___x_399_, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1___boxed(lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1();
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRci(lean_object* v_x_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRci___closed__1));
lean_inc(v_x_408_);
v___x_412_ = l_Lean_Syntax_isOfKind(v_x_408_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_x_408_);
v___x_413_ = l_Lean_Fmt_Error_partialFormatter;
v___x_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v_a_410_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_opTk_418_; lean_object* v___x_419_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = l_Lean_Syntax_getArg(v_x_408_, v___x_415_);
v___x_417_ = lean_unsigned_to_nat(1u);
v_opTk_418_ = l_Lean_Syntax_getArg(v_x_408_, v___x_417_);
lean_dec(v_x_408_);
v___x_419_ = l_Lean_Fmt_fmtPostfixRange(v___x_416_, v_opTk_418_, v_a_409_, v_a_410_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRci___boxed(lean_object* v_x_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Fmt_fmtRangeRci(v_x_420_, v_a_421_, v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1(){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_430_ = l_Lean_Fmt_fmtAttribute;
v___x_431_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRci___closed__1));
v___x_432_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___closed__1));
v___x_433_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRci___boxed), 3, 0);
v___x_434_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_430_, v___x_431_, v___x_432_, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1___boxed(lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1();
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoi(lean_object* v_x_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRoi___closed__1));
lean_inc(v_x_441_);
v___x_445_ = l_Lean_Syntax_isOfKind(v_x_441_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_x_441_);
v___x_446_ = l_Lean_Fmt_Error_partialFormatter;
v___x_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v_a_443_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_opTk_451_; lean_object* v___x_452_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = l_Lean_Syntax_getArg(v_x_441_, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(1u);
v_opTk_451_ = l_Lean_Syntax_getArg(v_x_441_, v___x_450_);
lean_dec(v_x_441_);
v___x_452_ = l_Lean_Fmt_fmtPostfixRange(v___x_449_, v_opTk_451_, v_a_442_, v_a_443_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRangeRoi___boxed(lean_object* v_x_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Fmt_fmtRangeRoi(v_x_453_, v_a_454_, v_a_455_);
lean_dec_ref(v_a_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1(){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_463_ = l_Lean_Fmt_fmtAttribute;
v___x_464_ = ((lean_object*)(l_Lean_Fmt_fmtRangeRoi___closed__1));
v___x_465_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___closed__1));
v___x_466_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRangeRoi___boxed), 3, 0);
v___x_467_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_463_, v___x_464_, v___x_465_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1___boxed(lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1();
return v_res_469_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRco___regBuiltin_Lean_Fmt_fmtRangeRco__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcoExcl___regBuiltin_Lean_Fmt_fmtRangeRcoExcl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRcc___regBuiltin_Lean_Fmt_fmtRangeRcc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoo___regBuiltin_Lean_Fmt_fmtRangeRoo__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRooExcl___regBuiltin_Lean_Fmt_fmtRangeRooExcl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoc___regBuiltin_Lean_Fmt_fmtRangeRoc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRio___regBuiltin_Lean_Fmt_fmtRangeRio__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRioExcl___regBuiltin_Lean_Fmt_fmtRangeRioExcl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRic___regBuiltin_Lean_Fmt_fmtRangeRic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRci___regBuiltin_Lean_Fmt_fmtRangeRci__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange_0__Lean_Fmt_fmtRangeRoi___regBuiltin_Lean_Fmt_fmtRangeRoi__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Data_Range_Polymorphic_PRange(builtin);
}
#ifdef __cplusplus
}
#endif
