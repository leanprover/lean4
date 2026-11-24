// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Grind.Attr
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Grind.Attr import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtGrindEq___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGrindEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtGrindEq___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Fmt_fmtGrindEq___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Fmt_fmtGrindEq___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindEq___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEq___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEq___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__3_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Fmt_fmtGrindEq___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtGrindEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Fmt_fmtGrindEq___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindEq___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEq___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEq___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__5_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Fmt_fmtGrindEq___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtGrindEq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 219, 190, 138, 103, 112, 129, 219)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindEqRhs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Fmt_fmtGrindEqRhs___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindEqRhs___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindEqRhs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEqRhs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEqRhs___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEqRhs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEqRhs___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEqRhs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEqRhs___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindEqRhs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Fmt_fmtGrindEqRhs___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindEqRhs___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqRhs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqRhs___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindEqRhs"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 99, 58, 77, 226, 6, 186, 235)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindEqBoth___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Fmt_fmtGrindEqBoth___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindEqBoth___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindEqBoth___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEqBoth___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEqBoth___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEqBoth___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEqBoth___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindEqBoth___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindEqBoth___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindEqBoth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Fmt_fmtGrindEqBoth___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindEqBoth___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqBoth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqBoth___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtGrindEqBoth"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 95, 207, 141, 207, 206, 71, 253)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqBwd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqBwd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindEqBwd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 153, 147, 64, 118, 21, 111, 178)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBwd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBwd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindBwd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 97, 141, 164, 21, 215, 165, 146)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDef___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindDef"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 223, 17, 125, 19, 201, 188, 86)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindCasesEager___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Fmt_fmtGrindCasesEager___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindCasesEager___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesEager___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesEager___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCasesEager___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesEager___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCasesEager___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindCasesEager___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindCasesEager___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindCasesEager___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Fmt_fmtGrindCasesEager___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindCasesEager___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCasesEager(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCasesEager___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtGrindCasesEager"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 26, 108, 250, 80, 179, 178, 234)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindHomFallback___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindHomFallback"};
static const lean_object* l_Lean_Fmt_fmtGrindHomFallback___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindHomFallback___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindHomFallback___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHomFallback___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHomFallback___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHomFallback___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHomFallback___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindHomFallback___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindHomFallback___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindHomFallback___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 210, 151, 50, 71, 98, 251, 189)}};
static const lean_object* l_Lean_Fmt_fmtGrindHomFallback___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindHomFallback___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHomFallback(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHomFallback___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindHomFallback"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 116, 230, 236, 72, 35, 83, 214)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNorm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNorm___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGrindNorm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 71, 28, 207, 124, 208, 142, 200)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindSym___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Fmt_fmtGrindSym___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindSym___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindSym___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSym___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSym___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSym___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSym___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindSym___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindSym___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindSym___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Fmt_fmtGrindSym___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindSym___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSym(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSym___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindSym"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 26, 108, 158, 149, 229, 54, 180)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Fmt_fmtGrindMod___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindMod___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindMod___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindMod___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindMod___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindMod___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindMod___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindMod___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Fmt_fmtGrindMod___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindMod___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindMod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindMod___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGrindMod"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 183, 4, 118, 9, 79, 173, 220)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Fmt_fmtGrindAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 96, 164, 147, 27, 132, 207, 84)}};
static const lean_object* l_Lean_Fmt_fmtGrindAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGrindAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 235, 170, 230, 44, 177, 26, 214)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindBangAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "grind!"};
static const lean_object* l_Lean_Fmt_fmtGrindBangAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindBangAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBangAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBangAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBangAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBangAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBangAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBangAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBangAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindBangAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 252, 17, 243, 124, 48, 8, 212)}};
static const lean_object* l_Lean_Fmt_fmtGrindBangAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindBangAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBangAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBangAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindBangAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 174, 100, 223, 255, 30, 160, 223)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindQuestionAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "grind\?"};
static const lean_object* l_Lean_Fmt_fmtGrindQuestionAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindQuestionAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindQuestionAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindQuestionAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindQuestionAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindQuestionAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindQuestionAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindQuestionAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindQuestionAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindQuestionAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 162, 0, 226, 225, 245, 191, 202)}};
static const lean_object* l_Lean_Fmt_fmtGrindQuestionAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindQuestionAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindQuestionAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindQuestionAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtGrindQuestionAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 127, 157, 65, 45, 153, 78, 140)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grind!\?"};
static const lean_object* l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 47, 189, 75, 111, 35, 109, 167)}};
static const lean_object* l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBangQuestionAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBangQuestionAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtGrindBangQuestionAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 62, 17, 234, 146, 13, 191, 154)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLiaAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Fmt_fmtLiaAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLiaAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLiaAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLiaAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 175, 201, 41, 164, 106, 123, 86)}};
static const lean_object* l_Lean_Fmt_fmtLiaAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLiaAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtLiaAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 97, 86, 193, 149, 169, 17, 242)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLiaBangAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lia!"};
static const lean_object* l_Lean_Fmt_fmtLiaBangAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLiaBangAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLiaBangAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaBangAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaBangAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaBangAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaBangAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaBangAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaBangAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLiaBangAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 230, 55, 89, 228, 207, 40, 70)}};
static const lean_object* l_Lean_Fmt_fmtLiaBangAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLiaBangAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaBangAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaBangAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtLiaBangAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 185, 90, 178, 37, 57, 94, 235)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLiaQuestionAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lia\?"};
static const lean_object* l_Lean_Fmt_fmtLiaQuestionAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLiaQuestionAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLiaQuestionAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaQuestionAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaQuestionAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaQuestionAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaQuestionAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaQuestionAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaQuestionAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLiaQuestionAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 19, 233, 46, 81, 4, 131, 84)}};
static const lean_object* l_Lean_Fmt_fmtLiaQuestionAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLiaQuestionAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaQuestionAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaQuestionAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtLiaQuestionAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 147, 25, 107, 2, 185, 87, 206)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lia!\?"};
static const lean_object* l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 225, 122, 223, 138, 249, 208, 101)}};
static const lean_object* l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaBangQuestionAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaBangQuestionAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtLiaBangQuestionAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 204, 204, 133, 95, 206, 192, 118)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEq(lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___y_20_; lean_object* v___y_21_; lean_object* v___y_22_; lean_object* v___y_23_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEq___closed__4));
lean_inc(v_x_16_);
v___x_37_ = l_Lean_Syntax_isOfKind(v_x_16_, v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_x_16_);
v___x_38_ = l_Lean_Fmt_Error_partialFormatter;
v___x_39_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v_a_18_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v_eqTk_41_; lean_object* v_gen_x3f_43_; lean_object* v___y_44_; lean_object* v___y_45_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_40_ = lean_unsigned_to_nat(0u);
v_eqTk_41_ = l_Lean_Syntax_getArg(v_x_16_, v___x_40_);
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = l_Lean_Syntax_getArg(v_x_16_, v___x_60_);
lean_dec(v_x_16_);
v___x_62_ = l_Lean_Syntax_isNone(v___x_61_);
if (v___x_62_ == 0)
{
uint8_t v___x_63_; 
lean_inc(v___x_61_);
v___x_63_ = l_Lean_Syntax_matchesNull(v___x_61_, v___x_60_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v___x_61_);
lean_dec(v_eqTk_41_);
v___x_64_ = l_Lean_Fmt_Error_partialFormatter;
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v_a_18_);
return v___x_65_;
}
else
{
lean_object* v_gen_x3f_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_gen_x3f_66_ = l_Lean_Syntax_getArg(v___x_61_, v___x_40_);
lean_dec(v___x_61_);
v___x_67_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEq___closed__6));
lean_inc(v_gen_x3f_66_);
v___x_68_ = l_Lean_Syntax_isOfKind(v_gen_x3f_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_gen_x3f_66_);
lean_dec(v_eqTk_41_);
v___x_69_ = l_Lean_Fmt_Error_partialFormatter;
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_a_18_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v_gen_x3f_66_);
v_gen_x3f_43_ = v___x_71_;
v___y_44_ = v_a_17_;
v___y_45_ = v_a_18_;
goto v___jp_42_;
}
}
}
else
{
lean_object* v___x_72_; 
lean_dec(v___x_61_);
v___x_72_ = lean_box(0);
v_gen_x3f_43_ = v___x_72_;
v___y_44_ = v_a_17_;
v___y_45_ = v_a_18_;
goto v___jp_42_;
}
v___jp_42_:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Fmt_fmt(v_eqTk_41_, v___y_44_, v___y_45_);
if (lean_obj_tag(v___x_46_) == 0)
{
if (lean_obj_tag(v_gen_x3f_43_) == 0)
{
lean_object* v_a_47_; lean_object* v_a_48_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
v_a_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_46_, 2);
v___x_49_ = lean_box(0);
v___y_20_ = v_a_48_;
v___y_21_ = v___y_44_;
v___y_22_ = v_a_47_;
v___y_23_ = v___x_49_;
goto v___jp_19_;
}
else
{
lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v_val_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
v_a_50_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_50_);
v_a_51_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_46_, 2);
v_val_52_ = lean_ctor_get(v_gen_x3f_43_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v_gen_x3f_43_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v_gen_x3f_43_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_val_52_);
lean_dec(v_gen_x3f_43_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_val_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
v___y_20_ = v_a_51_;
v___y_21_ = v___y_44_;
v___y_22_ = v_a_50_;
v___y_23_ = v___x_57_;
goto v___jp_19_;
}
}
}
}
else
{
lean_dec(v_gen_x3f_43_);
return v___x_46_;
}
}
}
v___jp_19_:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Fmt_fmt_x3f(v___y_23_, v___y_21_, v___y_20_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_35_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_a_26_ = lean_ctor_get(v___x_24_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_35_ == 0)
{
v___x_28_ = v___x_24_;
v_isShared_29_ = v_isSharedCheck_35_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_35_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_30_ = 2;
v___x_31_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_22_, v_a_25_, v___x_30_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_31_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_a_26_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
else
{
lean_dec_ref(v___y_22_);
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEq___boxed(lean_object* v_x_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Fmt_fmtGrindEq(v_x_73_, v_a_74_, v_a_75_);
lean_dec_ref(v_a_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1(){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = l_Lean_Fmt_fmtAttribute;
v___x_85_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEq___closed__4));
v___x_86_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___closed__2));
v___x_87_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindEq___boxed), 3, 0);
v___x_88_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_84_, v___x_85_, v___x_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1___boxed(lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqRhs(lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEqRhs___closed__1));
lean_inc(v_x_97_);
v___x_124_ = l_Lean_Syntax_isOfKind(v_x_97_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_x_97_);
v___x_125_ = l_Lean_Fmt_Error_partialFormatter;
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v_a_99_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v_eqTk_128_; lean_object* v___x_129_; lean_object* v_underTk_130_; lean_object* v_gen_x3f_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v_eqTk_128_ = l_Lean_Syntax_getArg(v_x_97_, v___x_127_);
v___x_129_ = lean_unsigned_to_nat(1u);
v_underTk_130_ = l_Lean_Syntax_getArg(v_x_97_, v___x_129_);
v___x_152_ = lean_unsigned_to_nat(2u);
v___x_153_ = l_Lean_Syntax_getArg(v_x_97_, v___x_152_);
lean_dec(v_x_97_);
v___x_154_ = l_Lean_Syntax_isNone(v___x_153_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
lean_inc(v___x_153_);
v___x_155_ = l_Lean_Syntax_matchesNull(v___x_153_, v___x_129_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v___x_153_);
lean_dec(v_underTk_130_);
lean_dec(v_eqTk_128_);
v___x_156_ = l_Lean_Fmt_Error_partialFormatter;
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_99_);
return v___x_157_;
}
else
{
lean_object* v_gen_x3f_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_gen_x3f_158_ = l_Lean_Syntax_getArg(v___x_153_, v___x_127_);
lean_dec(v___x_153_);
v___x_159_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEq___closed__6));
lean_inc(v_gen_x3f_158_);
v___x_160_ = l_Lean_Syntax_isOfKind(v_gen_x3f_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_gen_x3f_158_);
lean_dec(v_underTk_130_);
lean_dec(v_eqTk_128_);
v___x_161_ = l_Lean_Fmt_Error_partialFormatter;
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_99_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_gen_x3f_158_);
v_gen_x3f_132_ = v___x_163_;
v___y_133_ = v_a_98_;
v___y_134_ = v_a_99_;
goto v___jp_131_;
}
}
}
else
{
lean_object* v___x_164_; 
lean_dec(v___x_153_);
v___x_164_ = lean_box(0);
v_gen_x3f_132_ = v___x_164_;
v___y_133_ = v_a_98_;
v___y_134_ = v_a_99_;
goto v___jp_131_;
}
v___jp_131_:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Fmt_fmt(v_eqTk_128_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v_a_137_; lean_object* v___x_138_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
v_a_137_ = lean_ctor_get(v___x_135_, 1);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_135_, 2);
v___x_138_ = l_Lean_Fmt_fmt(v_underTk_130_, v___y_133_, v_a_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
if (lean_obj_tag(v_gen_x3f_132_) == 0)
{
lean_object* v_a_139_; lean_object* v_a_140_; lean_object* v___x_141_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
v_a_140_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_a_140_);
lean_dec_ref_known(v___x_138_, 2);
v___x_141_ = lean_box(0);
v___y_101_ = v_a_136_;
v___y_102_ = v_a_140_;
v___y_103_ = v_a_139_;
v___y_104_ = v___y_133_;
v___y_105_ = v___x_141_;
goto v___jp_100_;
}
else
{
lean_object* v_a_142_; lean_object* v_a_143_; lean_object* v_val_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_142_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_142_);
v_a_143_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_138_, 2);
v_val_144_ = lean_ctor_get(v_gen_x3f_132_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_gen_x3f_132_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v_gen_x3f_132_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_val_144_);
lean_dec(v_gen_x3f_132_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_val_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
v___y_101_ = v_a_136_;
v___y_102_ = v_a_143_;
v___y_103_ = v_a_142_;
v___y_104_ = v___y_133_;
v___y_105_ = v___x_149_;
goto v___jp_100_;
}
}
}
}
else
{
lean_dec(v_a_136_);
lean_dec(v_gen_x3f_132_);
return v___x_138_;
}
}
else
{
lean_dec(v_gen_x3f_132_);
lean_dec(v_underTk_130_);
return v___x_135_;
}
}
}
v___jp_100_:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Fmt_fmt_x3f(v___y_105_, v___y_104_, v___y_102_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_122_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_a_108_ = lean_ctor_get(v___x_106_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_122_ == 0)
{
v___x_110_ = v___x_106_;
v_isShared_111_ = v_isSharedCheck_122_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_122_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_112_ = lean_unsigned_to_nat(2u);
v___x_113_ = lean_mk_empty_array_with_capacity(v___x_112_);
v___x_114_ = lean_array_push(v___x_113_, v___y_101_);
v___x_115_ = lean_array_push(v___x_114_, v___y_103_);
v___x_116_ = l_Lean_Fmt_Layouts_atomic(v___x_115_);
lean_dec_ref(v___x_115_);
v___x_117_ = 2;
v___x_118_ = l_Lean_Fmt_Layouts_prefixOperator(v___x_116_, v_a_107_, v___x_117_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_118_);
v___x_120_ = v___x_110_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_a_108_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_dec_ref(v___y_103_);
lean_dec_ref(v___y_101_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqRhs___boxed(lean_object* v_x_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Fmt_fmtGrindEqRhs(v_x_165_, v_a_166_, v_a_167_);
lean_dec_ref(v_a_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1(){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_175_ = l_Lean_Fmt_fmtAttribute;
v___x_176_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEqRhs___closed__1));
v___x_177_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___closed__1));
v___x_178_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindEqRhs___boxed), 3, 0);
v___x_179_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_175_, v___x_176_, v___x_177_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1___boxed(lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1();
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqBoth(lean_object* v_x_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEqBoth___closed__1));
lean_inc(v_x_188_);
v___x_217_ = l_Lean_Syntax_isOfKind(v_x_188_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_x_188_);
v___x_218_ = l_Lean_Fmt_Error_partialFormatter;
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_a_190_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v_u1_221_; lean_object* v___x_222_; lean_object* v_eqTk_223_; lean_object* v___x_224_; lean_object* v_u2_225_; lean_object* v_gen_x3f_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v_u1_221_ = l_Lean_Syntax_getArg(v_x_188_, v___x_220_);
v___x_222_ = lean_unsigned_to_nat(1u);
v_eqTk_223_ = l_Lean_Syntax_getArg(v_x_188_, v___x_222_);
v___x_224_ = lean_unsigned_to_nat(2u);
v_u2_225_ = l_Lean_Syntax_getArg(v_x_188_, v___x_224_);
v___x_250_ = lean_unsigned_to_nat(3u);
v___x_251_ = l_Lean_Syntax_getArg(v_x_188_, v___x_250_);
lean_dec(v_x_188_);
v___x_252_ = l_Lean_Syntax_isNone(v___x_251_);
if (v___x_252_ == 0)
{
uint8_t v___x_253_; 
lean_inc(v___x_251_);
v___x_253_ = l_Lean_Syntax_matchesNull(v___x_251_, v___x_222_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_251_);
lean_dec(v_u2_225_);
lean_dec(v_eqTk_223_);
lean_dec(v_u1_221_);
v___x_254_ = l_Lean_Fmt_Error_partialFormatter;
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_190_);
return v___x_255_;
}
else
{
lean_object* v_gen_x3f_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_gen_x3f_256_ = l_Lean_Syntax_getArg(v___x_251_, v___x_220_);
lean_dec(v___x_251_);
v___x_257_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEq___closed__6));
lean_inc(v_gen_x3f_256_);
v___x_258_ = l_Lean_Syntax_isOfKind(v_gen_x3f_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_gen_x3f_256_);
lean_dec(v_u2_225_);
lean_dec(v_eqTk_223_);
lean_dec(v_u1_221_);
v___x_259_ = l_Lean_Fmt_Error_partialFormatter;
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_a_190_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_gen_x3f_256_);
v_gen_x3f_227_ = v___x_261_;
v___y_228_ = v_a_189_;
v___y_229_ = v_a_190_;
goto v___jp_226_;
}
}
}
else
{
lean_object* v___x_262_; 
lean_dec(v___x_251_);
v___x_262_ = lean_box(0);
v_gen_x3f_227_ = v___x_262_;
v___y_228_ = v_a_189_;
v___y_229_ = v_a_190_;
goto v___jp_226_;
}
v___jp_226_:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Fmt_fmt(v_u1_221_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
v_a_232_ = lean_ctor_get(v___x_230_, 1);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_230_, 2);
v___x_233_ = l_Lean_Fmt_fmt(v_eqTk_223_, v___y_228_, v_a_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v_a_235_; lean_object* v___x_236_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
v_a_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_233_, 2);
v___x_236_ = l_Lean_Fmt_fmt(v_u2_225_, v___y_228_, v_a_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
if (lean_obj_tag(v_gen_x3f_227_) == 0)
{
lean_object* v_a_237_; lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
v_a_238_ = lean_ctor_get(v___x_236_, 1);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_236_, 2);
v___x_239_ = lean_box(0);
v___y_192_ = v_a_237_;
v___y_193_ = v_a_238_;
v___y_194_ = v___y_228_;
v___y_195_ = v_a_234_;
v___y_196_ = v_a_231_;
v___y_197_ = v___x_239_;
goto v___jp_191_;
}
else
{
lean_object* v_a_240_; lean_object* v_a_241_; lean_object* v_val_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_240_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_240_);
v_a_241_ = lean_ctor_get(v___x_236_, 1);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_236_, 2);
v_val_242_ = lean_ctor_get(v_gen_x3f_227_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_gen_x3f_227_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v_gen_x3f_227_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_val_242_);
lean_dec(v_gen_x3f_227_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_val_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
v___y_192_ = v_a_240_;
v___y_193_ = v_a_241_;
v___y_194_ = v___y_228_;
v___y_195_ = v_a_234_;
v___y_196_ = v_a_231_;
v___y_197_ = v___x_247_;
goto v___jp_191_;
}
}
}
}
else
{
lean_dec(v_a_234_);
lean_dec(v_a_231_);
lean_dec(v_gen_x3f_227_);
return v___x_236_;
}
}
else
{
lean_dec(v_a_231_);
lean_dec(v_gen_x3f_227_);
lean_dec(v_u2_225_);
return v___x_233_;
}
}
else
{
lean_dec(v_gen_x3f_227_);
lean_dec(v_u2_225_);
lean_dec(v_eqTk_223_);
return v___x_230_;
}
}
}
v___jp_191_:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Fmt_fmt_x3f(v___y_197_, v___y_194_, v___y_193_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_215_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_a_200_ = lean_ctor_get(v___x_198_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_215_ == 0)
{
v___x_202_ = v___x_198_;
v_isShared_203_ = v_isSharedCheck_215_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_215_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_204_ = lean_unsigned_to_nat(3u);
v___x_205_ = lean_mk_empty_array_with_capacity(v___x_204_);
v___x_206_ = lean_array_push(v___x_205_, v___y_196_);
v___x_207_ = lean_array_push(v___x_206_, v___y_195_);
v___x_208_ = lean_array_push(v___x_207_, v___y_192_);
v___x_209_ = l_Lean_Fmt_Layouts_atomic(v___x_208_);
lean_dec_ref(v___x_208_);
v___x_210_ = 2;
v___x_211_ = l_Lean_Fmt_Layouts_prefixOperator(v___x_209_, v_a_199_, v___x_210_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_211_);
v___x_213_ = v___x_202_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_a_200_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_dec_ref(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec_ref(v___y_192_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqBoth___boxed(lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Fmt_fmtGrindEqBoth(v_x_263_, v_a_264_, v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1(){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = l_Lean_Fmt_fmtAttribute;
v___x_274_ = ((lean_object*)(l_Lean_Fmt_fmtGrindEqBoth___closed__1));
v___x_275_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___closed__1));
v___x_276_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindEqBoth___boxed), 3, 0);
v___x_277_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_273_, v___x_274_, v___x_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1___boxed(lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1();
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqBwd(lean_object* v_stx_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_280_, v___x_283_, v_a_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v_a_286_; lean_object* v___x_287_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
v_a_286_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_284_, 2);
v___x_287_ = l_Lean_Fmt_getStxArg_x21___redArg(v_a_285_, v___x_283_, v_a_286_);
lean_dec(v_a_285_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v_a_289_; lean_object* v___x_290_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
v_a_289_ = lean_ctor_get(v___x_287_, 1);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_287_, 2);
v___x_290_ = l_Lean_Fmt_getStxArg_x21___redArg(v_a_288_, v___x_283_, v_a_289_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v_a_292_; lean_object* v___x_293_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
v_a_292_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_a_292_);
lean_dec_ref_known(v___x_290_, 2);
v___x_293_ = l_Lean_Fmt_fmt(v_a_291_, v_a_281_, v_a_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
v_a_295_ = lean_ctor_get(v___x_293_, 1);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_293_, 2);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = l_Lean_Fmt_getStxArg_x21___redArg(v_a_288_, v___x_296_, v_a_295_);
lean_dec(v_a_288_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
v_a_299_ = lean_ctor_get(v___x_297_, 1);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_297_, 2);
v___x_300_ = l_Lean_Fmt_fmt(v_a_298_, v_a_281_, v_a_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_314_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_a_302_ = lean_ctor_get(v___x_300_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_314_ == 0)
{
v___x_304_ = v___x_300_;
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_306_ = lean_unsigned_to_nat(2u);
v___x_307_ = lean_mk_empty_array_with_capacity(v___x_306_);
v___x_308_ = lean_array_push(v___x_307_, v_a_294_);
v___x_309_ = lean_array_push(v___x_308_, v_a_301_);
v___x_310_ = l_Lean_Fmt_Layouts_atomic(v___x_309_);
lean_dec_ref(v___x_309_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_310_);
v___x_312_ = v___x_304_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_a_302_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_dec(v_a_294_);
return v___x_300_;
}
}
else
{
lean_object* v_a_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_a_294_);
v_a_315_ = lean_ctor_get(v___x_297_, 0);
v_a_316_ = lean_ctor_get(v___x_297_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_297_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_inc(v_a_315_);
lean_dec(v___x_297_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_315_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_dec(v_a_288_);
return v___x_293_;
}
}
else
{
lean_object* v_a_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec(v_a_288_);
v_a_324_ = lean_ctor_get(v___x_290_, 0);
v_a_325_ = lean_ctor_get(v___x_290_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_290_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_inc(v_a_324_);
lean_dec(v___x_290_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_324_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_333_ = lean_ctor_get(v___x_287_, 0);
v_a_334_ = lean_ctor_get(v___x_287_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_287_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_inc(v_a_333_);
lean_dec(v___x_287_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_333_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_342_ = lean_ctor_get(v___x_284_, 0);
v_a_343_ = lean_ctor_get(v___x_284_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_284_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_inc(v_a_342_);
lean_dec(v___x_284_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_342_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindEqBwd___boxed(lean_object* v_stx_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Fmt_fmtGrindEqBwd(v_stx_351_, v_a_352_, v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_stx_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1(){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_367_ = l_Lean_Fmt_fmtAttribute;
v___x_368_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__1));
v___x_369_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___closed__3));
v___x_370_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindEqBwd___boxed), 3, 0);
v___x_371_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_367_, v___x_368_, v___x_369_, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1___boxed(lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1();
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBwd(lean_object* v_stx_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_374_, v___x_377_, v_a_376_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
v_a_380_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_378_, 2);
v___x_381_ = l_Lean_Fmt_fmtAtomic(v_a_379_, v_a_375_, v_a_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v_a_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
v_a_383_ = lean_ctor_get(v___x_381_, 1);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_381_, 2);
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_374_, v___x_384_, v_a_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v_a_387_; lean_object* v___y_389_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
v_a_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_385_, 2);
v___x_402_ = l_Lean_Syntax_getArgs(v_a_386_);
lean_dec(v_a_386_);
v___x_403_ = lean_array_get_size(v___x_402_);
v___x_404_ = lean_nat_dec_lt(v___x_377_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v___x_402_);
v___x_405_ = lean_box(0);
v___y_389_ = v___x_405_;
goto v___jp_388_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_array_fget(v___x_402_, v___x_377_);
lean_dec_ref(v___x_402_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___y_389_ = v___x_407_;
goto v___jp_388_;
}
v___jp_388_:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Fmt_fmt_x3f(v___y_389_, v_a_375_, v_a_387_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_401_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_a_392_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_401_ == 0)
{
v___x_394_ = v___x_390_;
v_isShared_395_ = v_isSharedCheck_401_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_401_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = 2;
v___x_397_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_382_, v_a_391_, v___x_396_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_397_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_a_392_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_dec(v_a_382_);
return v___x_390_;
}
}
}
else
{
lean_object* v_a_408_; lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_a_382_);
v_a_408_ = lean_ctor_get(v___x_385_, 0);
v_a_409_ = lean_ctor_get(v___x_385_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_385_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_inc(v_a_408_);
lean_dec(v___x_385_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
return v___x_381_;
}
}
else
{
lean_object* v_a_417_; lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_a_417_ = lean_ctor_get(v___x_378_, 0);
v_a_418_ = lean_ctor_get(v___x_378_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_378_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_inc(v_a_417_);
lean_dec(v___x_378_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_417_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBwd___boxed(lean_object* v_stx_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Fmt_fmtGrindBwd(v_stx_426_, v_a_427_, v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_stx_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1(){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_442_ = l_Lean_Fmt_fmtAttribute;
v___x_443_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__1));
v___x_444_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___closed__3));
v___x_445_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindBwd___boxed), 3, 0);
v___x_446_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_442_, v___x_443_, v___x_444_, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1___boxed(lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1();
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDef(lean_object* v_stx_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_449_, v___x_452_, v_a_451_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v_a_455_; lean_object* v___x_456_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
v_a_455_ = lean_ctor_get(v___x_453_, 1);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_453_, 2);
v___x_456_ = l_Lean_Fmt_fmtAtomic(v_a_454_, v_a_450_, v_a_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v_a_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
v_a_458_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_456_, 2);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_449_, v___x_459_, v_a_458_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v_a_462_; lean_object* v___y_464_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
v_a_462_ = lean_ctor_get(v___x_460_, 1);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_460_, 2);
v___x_477_ = l_Lean_Syntax_getArgs(v_a_461_);
lean_dec(v_a_461_);
v___x_478_ = lean_array_get_size(v___x_477_);
v___x_479_ = lean_nat_dec_lt(v___x_452_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec_ref(v___x_477_);
v___x_480_ = lean_box(0);
v___y_464_ = v___x_480_;
goto v___jp_463_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_array_fget(v___x_477_, v___x_452_);
lean_dec_ref(v___x_477_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___y_464_ = v___x_482_;
goto v___jp_463_;
}
v___jp_463_:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Fmt_fmt_x3f(v___y_464_, v_a_450_, v_a_462_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_476_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_a_467_ = lean_ctor_get(v___x_465_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_476_ == 0)
{
v___x_469_ = v___x_465_;
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = 2;
v___x_472_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_457_, v_a_466_, v___x_471_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_a_467_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
else
{
lean_dec(v_a_457_);
return v___x_465_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v_a_457_);
v_a_483_ = lean_ctor_get(v___x_460_, 0);
v_a_484_ = lean_ctor_get(v___x_460_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_460_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_inc(v_a_483_);
lean_dec(v___x_460_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_483_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
return v___x_456_;
}
}
else
{
lean_object* v_a_492_; lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_492_ = lean_ctor_get(v___x_453_, 0);
v_a_493_ = lean_ctor_get(v___x_453_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_453_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_inc(v_a_492_);
lean_dec(v___x_453_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_492_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindDef___boxed(lean_object* v_stx_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Fmt_fmtGrindDef(v_stx_501_, v_a_502_, v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_stx_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1(){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_517_ = l_Lean_Fmt_fmtAttribute;
v___x_518_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__1));
v___x_519_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___closed__3));
v___x_520_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindDef___boxed), 3, 0);
v___x_521_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_517_, v___x_518_, v___x_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1___boxed(lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1();
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCasesEager(lean_object* v_x_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Fmt_fmtGrindCasesEager___closed__1));
lean_inc(v_x_530_);
v___x_534_ = l_Lean_Syntax_isOfKind(v_x_530_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_x_530_);
v___x_535_ = l_Lean_Fmt_Error_partialFormatter;
v___x_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v_a_532_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; lean_object* v_casesTk_538_; lean_object* v___x_539_; 
v___x_537_ = lean_unsigned_to_nat(0u);
v_casesTk_538_ = l_Lean_Syntax_getArg(v_x_530_, v___x_537_);
v___x_539_ = l_Lean_Fmt_fmt(v_casesTk_538_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v_a_541_; lean_object* v___x_542_; lean_object* v_eagerTk_543_; lean_object* v___x_544_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
v_a_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_539_, 2);
v___x_542_ = lean_unsigned_to_nat(1u);
v_eagerTk_543_ = l_Lean_Syntax_getArg(v_x_530_, v___x_542_);
lean_dec(v_x_530_);
v___x_544_ = l_Lean_Fmt_fmt(v_eagerTk_543_, v_a_531_, v_a_541_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_558_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_a_546_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_558_ == 0)
{
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_558_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_558_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = lean_mk_empty_array_with_capacity(v___x_550_);
v___x_552_ = lean_array_push(v___x_551_, v_a_540_);
v___x_553_ = lean_array_push(v___x_552_, v_a_545_);
v___x_554_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_553_);
lean_dec_ref(v___x_553_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_554_);
v___x_556_ = v___x_548_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_a_546_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_dec(v_a_540_);
return v___x_544_;
}
}
else
{
lean_dec(v_x_530_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindCasesEager___boxed(lean_object* v_x_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Fmt_fmtGrindCasesEager(v_x_559_, v_a_560_, v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1(){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_569_ = l_Lean_Fmt_fmtAttribute;
v___x_570_ = ((lean_object*)(l_Lean_Fmt_fmtGrindCasesEager___closed__1));
v___x_571_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___closed__1));
v___x_572_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindCasesEager___boxed), 3, 0);
v___x_573_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_569_, v___x_570_, v___x_571_, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1___boxed(lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1();
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHomFallback(lean_object* v_x_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_Fmt_fmtGrindHomFallback___closed__1));
lean_inc(v_x_582_);
v___x_586_ = l_Lean_Syntax_isOfKind(v_x_582_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_x_582_);
v___x_587_ = l_Lean_Fmt_Error_partialFormatter;
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_a_584_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v_homTk_590_; lean_object* v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v_homTk_590_ = l_Lean_Syntax_getArg(v_x_582_, v___x_589_);
v___x_591_ = l_Lean_Fmt_fmt(v_homTk_590_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v_fallbackTk_595_; lean_object* v___x_596_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
v_a_593_ = lean_ctor_get(v___x_591_, 1);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_591_, 2);
v___x_594_ = lean_unsigned_to_nat(1u);
v_fallbackTk_595_ = l_Lean_Syntax_getArg(v_x_582_, v___x_594_);
lean_dec(v_x_582_);
v___x_596_ = l_Lean_Fmt_fmt(v_fallbackTk_595_, v_a_583_, v_a_593_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_610_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_a_598_ = lean_ctor_get(v___x_596_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_610_ == 0)
{
v___x_600_ = v___x_596_;
v_isShared_601_ = v_isSharedCheck_610_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_610_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_602_ = lean_unsigned_to_nat(2u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
v___x_604_ = lean_array_push(v___x_603_, v_a_592_);
v___x_605_ = lean_array_push(v___x_604_, v_a_597_);
v___x_606_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_605_);
lean_dec_ref(v___x_605_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_606_);
v___x_608_ = v___x_600_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_a_598_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_dec(v_a_592_);
return v___x_596_;
}
}
else
{
lean_dec(v_x_582_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindHomFallback___boxed(lean_object* v_x_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Fmt_fmtGrindHomFallback(v_x_611_, v_a_612_, v_a_613_);
lean_dec_ref(v_a_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1(){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_621_ = l_Lean_Fmt_fmtAttribute;
v___x_622_ = ((lean_object*)(l_Lean_Fmt_fmtGrindHomFallback___closed__1));
v___x_623_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___closed__1));
v___x_624_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindHomFallback___boxed), 3, 0);
v___x_625_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_621_, v___x_622_, v___x_623_, v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1___boxed(lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1();
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNorm(lean_object* v_stx_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_628_, v___x_631_, v_a_630_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
v_a_634_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_632_, 2);
v___x_635_ = l_Lean_Fmt_fmt(v_a_633_, v_a_629_, v_a_634_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_699_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_a_637_ = lean_ctor_get(v___x_635_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_699_ == 0)
{
v___x_639_ = v___x_635_;
v_isShared_640_ = v_isSharedCheck_699_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_699_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___y_642_; lean_object* v_arrow_x3f_643_; lean_object* v___y_644_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_628_, v___x_654_, v_a_637_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___y_659_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
v_a_657_ = lean_ctor_get(v___x_655_, 1);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_655_, 2);
v___x_684_ = l_Lean_Syntax_getArgs(v_a_656_);
lean_dec(v_a_656_);
v___x_685_ = lean_array_get_size(v___x_684_);
v___x_686_ = lean_nat_dec_lt(v___x_631_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
lean_dec_ref(v___x_684_);
v___x_687_ = lean_box(0);
v___y_659_ = v___x_687_;
goto v___jp_658_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_array_fget(v___x_684_, v___x_631_);
lean_dec_ref(v___x_684_);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
v___y_659_ = v___x_689_;
goto v___jp_658_;
}
v___jp_658_:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Fmt_fmt_x3f(v___y_659_, v_a_629_, v_a_657_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
v_a_662_ = lean_ctor_get(v___x_660_, 1);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_660_, 2);
v___x_663_ = lean_unsigned_to_nat(2u);
v___x_664_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_628_, v___x_663_, v_a_662_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
v_a_666_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_664_, 2);
v___x_667_ = l_Lean_Syntax_getArgs(v_a_665_);
lean_dec(v_a_665_);
v___x_668_ = lean_array_get_size(v___x_667_);
v___x_669_ = lean_nat_dec_lt(v___x_631_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec_ref(v___x_667_);
v___x_670_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_642_ = v_a_661_;
v_arrow_x3f_643_ = v___x_670_;
v___y_644_ = v_a_666_;
goto v___jp_641_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_array_fget(v___x_667_, v___x_631_);
lean_dec_ref(v___x_667_);
v___x_672_ = l_Lean_Fmt_fmtAtomic(v___x_671_, v_a_629_, v_a_666_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v_a_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
v_a_674_ = lean_ctor_get(v___x_672_, 1);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_672_, 2);
v___y_642_ = v_a_661_;
v_arrow_x3f_643_ = v_a_673_;
v___y_644_ = v_a_674_;
goto v___jp_641_;
}
else
{
lean_dec(v_a_661_);
lean_del_object(v___x_639_);
lean_dec(v_a_636_);
return v___x_672_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_a_661_);
lean_del_object(v___x_639_);
lean_dec(v_a_636_);
v_a_675_ = lean_ctor_get(v___x_664_, 0);
v_a_676_ = lean_ctor_get(v___x_664_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_664_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_inc(v_a_675_);
lean_dec(v___x_664_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_del_object(v___x_639_);
lean_dec(v_a_636_);
return v___x_660_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_del_object(v___x_639_);
lean_dec(v_a_636_);
v_a_690_ = lean_ctor_get(v___x_655_, 0);
v_a_691_ = lean_ctor_get(v___x_655_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_655_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_inc(v_a_690_);
lean_dec(v___x_655_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_690_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
v___jp_641_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_645_ = lean_unsigned_to_nat(3u);
v___x_646_ = lean_mk_empty_array_with_capacity(v___x_645_);
v___x_647_ = lean_array_push(v___x_646_, v_a_636_);
v___x_648_ = lean_array_push(v___x_647_, v___y_642_);
v___x_649_ = lean_array_push(v___x_648_, v_arrow_x3f_643_);
v___x_650_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_649_);
lean_dec_ref(v___x_649_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___y_644_);
lean_ctor_set(v___x_639_, 0, v___x_650_);
v___x_652_ = v___x_639_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___y_644_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
return v___x_635_;
}
}
else
{
lean_object* v_a_700_; lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_700_ = lean_ctor_get(v___x_632_, 0);
v_a_701_ = lean_ctor_get(v___x_632_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_632_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_inc(v_a_700_);
lean_dec(v___x_632_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindNorm___boxed(lean_object* v_stx_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Fmt_fmtGrindNorm(v_stx_709_, v_a_710_, v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_stx_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1(){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_725_ = l_Lean_Fmt_fmtAttribute;
v___x_726_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__1));
v___x_727_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___closed__3));
v___x_728_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindNorm___boxed), 3, 0);
v___x_729_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_725_, v___x_726_, v___x_727_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1___boxed(lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1();
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSym(lean_object* v_x_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSym___closed__1));
lean_inc(v_x_738_);
v___x_742_ = l_Lean_Syntax_isOfKind(v_x_738_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec(v_x_738_);
v___x_743_ = l_Lean_Fmt_Error_partialFormatter;
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v_a_740_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v_symbolTk_746_; lean_object* v___x_747_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v_symbolTk_746_ = l_Lean_Syntax_getArg(v_x_738_, v___x_745_);
v___x_747_ = l_Lean_Fmt_fmt(v_symbolTk_746_, v_a_739_, v_a_740_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
v_a_749_ = lean_ctor_get(v___x_747_, 1);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_747_, 2);
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = l_Lean_Syntax_getArg(v_x_738_, v___x_750_);
lean_dec(v_x_738_);
v___x_752_ = l_Lean_Fmt_fmt(v___x_751_, v_a_739_, v_a_749_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_768_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_a_754_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_768_ == 0)
{
v___x_756_ = v___x_752_;
v_isShared_757_ = v_isSharedCheck_768_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_768_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_758_ = lean_unsigned_to_nat(2u);
v___x_759_ = lean_mk_empty_array_with_capacity(v___x_758_);
v___x_760_ = lean_array_push(v___x_759_, v_a_748_);
v___x_761_ = lean_array_push(v___x_760_, v_a_753_);
v___x_762_ = 0;
v___x_763_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_763_, 0, v___x_742_);
lean_ctor_set_uint8(v___x_763_, 1, v___x_762_);
lean_ctor_set_uint8(v___x_763_, 2, v___x_762_);
lean_ctor_set_uint8(v___x_763_, 3, v___x_762_);
v___x_764_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_761_, v___x_763_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_764_);
v___x_766_ = v___x_756_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_a_754_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_dec(v_a_748_);
return v___x_752_;
}
}
else
{
lean_dec(v_x_738_);
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindSym___boxed(lean_object* v_x_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Fmt_fmtGrindSym(v_x_769_, v_a_770_, v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1(){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_779_ = l_Lean_Fmt_fmtAttribute;
v___x_780_ = ((lean_object*)(l_Lean_Fmt_fmtGrindSym___closed__1));
v___x_781_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___closed__1));
v___x_782_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindSym___boxed), 3, 0);
v___x_783_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_779_, v___x_780_, v___x_781_, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1___boxed(lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1();
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindMod(lean_object* v_x_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_x_792_);
v___x_796_ = l_Lean_Syntax_isOfKind(v_x_792_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v_x_792_);
v___x_797_ = l_Lean_Fmt_Error_partialFormatter;
v___x_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_a_794_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = l_Lean_Syntax_getArg(v_x_792_, v___x_799_);
lean_dec(v_x_792_);
v___x_801_ = l_Lean_Fmt_fmt(v___x_800_, v_a_793_, v_a_794_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindMod___boxed(lean_object* v_x_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Fmt_fmtGrindMod(v_x_802_, v_a_803_, v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1(){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_812_ = l_Lean_Fmt_fmtAttribute;
v___x_813_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
v___x_814_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___closed__1));
v___x_815_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindMod___boxed), 3, 0);
v___x_816_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_812_, v___x_813_, v___x_814_, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1___boxed(lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1();
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAttr(lean_object* v_x_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; 
v___x_828_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAttr___closed__1));
lean_inc(v_x_825_);
v___x_829_ = l_Lean_Syntax_isOfKind(v_x_825_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_x_825_);
v___x_852_ = l_Lean_Fmt_Error_partialFormatter;
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_a_827_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v_grindTk_855_; lean_object* v_mod_x3f_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v_grindTk_855_ = l_Lean_Syntax_getArg(v_x_825_, v___x_854_);
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = l_Lean_Syntax_getArg(v_x_825_, v___x_874_);
lean_dec(v_x_825_);
v___x_876_ = l_Lean_Syntax_isNone(v___x_875_);
if (v___x_876_ == 0)
{
uint8_t v___x_877_; 
lean_inc(v___x_875_);
v___x_877_ = l_Lean_Syntax_matchesNull(v___x_875_, v___x_874_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v___x_875_);
lean_dec(v_grindTk_855_);
v___x_878_ = l_Lean_Fmt_Error_partialFormatter;
v___x_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v_a_827_);
return v___x_879_;
}
else
{
lean_object* v_mod_x3f_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_mod_x3f_880_ = l_Lean_Syntax_getArg(v___x_875_, v___x_854_);
lean_dec(v___x_875_);
v___x_881_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_mod_x3f_880_);
v___x_882_ = l_Lean_Syntax_isOfKind(v_mod_x3f_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec(v_mod_x3f_880_);
lean_dec(v_grindTk_855_);
v___x_883_ = l_Lean_Fmt_Error_partialFormatter;
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_a_827_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_mod_x3f_880_);
v_mod_x3f_857_ = v___x_885_;
v___y_858_ = v_a_826_;
v___y_859_ = v_a_827_;
goto v___jp_856_;
}
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v___x_875_);
v___x_886_ = lean_box(0);
v_mod_x3f_857_ = v___x_886_;
v___y_858_ = v_a_826_;
v___y_859_ = v_a_827_;
goto v___jp_856_;
}
v___jp_856_:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Fmt_fmt(v_grindTk_855_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
if (lean_obj_tag(v_mod_x3f_857_) == 0)
{
lean_object* v_a_861_; lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
v_a_862_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_860_, 2);
v___x_863_ = lean_box(0);
v___y_831_ = v_a_861_;
v___y_832_ = v___y_858_;
v___y_833_ = v_a_862_;
v___y_834_ = v___x_863_;
goto v___jp_830_;
}
else
{
lean_object* v_a_864_; lean_object* v_a_865_; lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_864_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_864_);
v_a_865_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_860_, 2);
v_val_866_ = lean_ctor_get(v_mod_x3f_857_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v_mod_x3f_857_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v_mod_x3f_857_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_dec(v_mod_x3f_857_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_val_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v___y_831_ = v_a_864_;
v___y_832_ = v___y_858_;
v___y_833_ = v_a_865_;
v___y_834_ = v___x_871_;
goto v___jp_830_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_857_);
return v___x_860_;
}
}
}
v___jp_830_:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Fmt_fmt_x3f(v___y_834_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_851_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_a_837_ = lean_ctor_get(v___x_835_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_851_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_851_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_851_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_841_ = lean_unsigned_to_nat(2u);
v___x_842_ = lean_mk_empty_array_with_capacity(v___x_841_);
v___x_843_ = lean_array_push(v___x_842_, v___y_831_);
v___x_844_ = lean_array_push(v___x_843_, v_a_836_);
v___x_845_ = 0;
v___x_846_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_846_, 0, v___x_829_);
lean_ctor_set_uint8(v___x_846_, 1, v___x_845_);
lean_ctor_set_uint8(v___x_846_, 2, v___x_845_);
lean_ctor_set_uint8(v___x_846_, 3, v___x_845_);
v___x_847_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_844_, v___x_846_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_847_);
v___x_849_ = v___x_839_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_a_837_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_dec_ref(v___y_831_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAttr___boxed(lean_object* v_x_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Fmt_fmtGrindAttr(v_x_887_, v_a_888_, v_a_889_);
lean_dec_ref(v_a_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1(){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_897_ = l_Lean_Fmt_fmtAttribute;
v___x_898_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAttr___closed__1));
v___x_899_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___closed__1));
v___x_900_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindAttr___boxed), 3, 0);
v___x_901_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_897_, v___x_898_, v___x_899_, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1___boxed(lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1();
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBangAttr(lean_object* v_x_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_913_; uint8_t v___x_914_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; 
v___x_913_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBangAttr___closed__1));
lean_inc(v_x_910_);
v___x_914_ = l_Lean_Syntax_isOfKind(v_x_910_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_x_910_);
v___x_937_ = l_Lean_Fmt_Error_partialFormatter;
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_a_912_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v_grindTk_940_; lean_object* v_mod_x3f_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v_grindTk_940_ = l_Lean_Syntax_getArg(v_x_910_, v___x_939_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = l_Lean_Syntax_getArg(v_x_910_, v___x_959_);
lean_dec(v_x_910_);
v___x_961_ = l_Lean_Syntax_isNone(v___x_960_);
if (v___x_961_ == 0)
{
uint8_t v___x_962_; 
lean_inc(v___x_960_);
v___x_962_ = l_Lean_Syntax_matchesNull(v___x_960_, v___x_959_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v___x_960_);
lean_dec(v_grindTk_940_);
v___x_963_ = l_Lean_Fmt_Error_partialFormatter;
v___x_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_a_912_);
return v___x_964_;
}
else
{
lean_object* v_mod_x3f_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_mod_x3f_965_ = l_Lean_Syntax_getArg(v___x_960_, v___x_939_);
lean_dec(v___x_960_);
v___x_966_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_mod_x3f_965_);
v___x_967_ = l_Lean_Syntax_isOfKind(v_mod_x3f_965_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v_mod_x3f_965_);
lean_dec(v_grindTk_940_);
v___x_968_ = l_Lean_Fmt_Error_partialFormatter;
v___x_969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v_a_912_);
return v___x_969_;
}
else
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v_mod_x3f_965_);
v_mod_x3f_942_ = v___x_970_;
v___y_943_ = v_a_911_;
v___y_944_ = v_a_912_;
goto v___jp_941_;
}
}
}
else
{
lean_object* v___x_971_; 
lean_dec(v___x_960_);
v___x_971_ = lean_box(0);
v_mod_x3f_942_ = v___x_971_;
v___y_943_ = v_a_911_;
v___y_944_ = v_a_912_;
goto v___jp_941_;
}
v___jp_941_:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Fmt_fmt(v_grindTk_940_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_945_) == 0)
{
if (lean_obj_tag(v_mod_x3f_942_) == 0)
{
lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v___x_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
v_a_947_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_945_, 2);
v___x_948_ = lean_box(0);
v___y_916_ = v_a_946_;
v___y_917_ = v___y_943_;
v___y_918_ = v_a_947_;
v___y_919_ = v___x_948_;
goto v___jp_915_;
}
else
{
lean_object* v_a_949_; lean_object* v_a_950_; lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_949_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_949_);
v_a_950_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_945_, 2);
v_val_951_ = lean_ctor_get(v_mod_x3f_942_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_mod_x3f_942_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v_mod_x3f_942_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v_mod_x3f_942_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_val_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
v___y_916_ = v_a_949_;
v___y_917_ = v___y_943_;
v___y_918_ = v_a_950_;
v___y_919_ = v___x_956_;
goto v___jp_915_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_942_);
return v___x_945_;
}
}
}
v___jp_915_:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Fmt_fmt_x3f(v___y_919_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_936_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_a_922_ = lean_ctor_get(v___x_920_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_936_ == 0)
{
v___x_924_ = v___x_920_;
v_isShared_925_ = v_isSharedCheck_936_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_936_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_926_ = lean_unsigned_to_nat(2u);
v___x_927_ = lean_mk_empty_array_with_capacity(v___x_926_);
v___x_928_ = lean_array_push(v___x_927_, v___y_916_);
v___x_929_ = lean_array_push(v___x_928_, v_a_921_);
v___x_930_ = 0;
v___x_931_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_931_, 0, v___x_914_);
lean_ctor_set_uint8(v___x_931_, 1, v___x_930_);
lean_ctor_set_uint8(v___x_931_, 2, v___x_930_);
lean_ctor_set_uint8(v___x_931_, 3, v___x_930_);
v___x_932_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_929_, v___x_931_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_932_);
v___x_934_ = v___x_924_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_a_922_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
else
{
lean_dec_ref(v___y_916_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBangAttr___boxed(lean_object* v_x_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Fmt_fmtGrindBangAttr(v_x_972_, v_a_973_, v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1(){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_982_ = l_Lean_Fmt_fmtAttribute;
v___x_983_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBangAttr___closed__1));
v___x_984_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___closed__1));
v___x_985_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindBangAttr___boxed), 3, 0);
v___x_986_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_982_, v___x_983_, v___x_984_, v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1___boxed(lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1();
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindQuestionAttr(lean_object* v_x_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; 
v___x_998_ = ((lean_object*)(l_Lean_Fmt_fmtGrindQuestionAttr___closed__1));
lean_inc(v_x_995_);
v___x_999_ = l_Lean_Syntax_isOfKind(v_x_995_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec(v_x_995_);
v___x_1022_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_a_997_);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; lean_object* v_grindTk_1025_; lean_object* v_mod_x3f_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v_grindTk_1025_ = l_Lean_Syntax_getArg(v_x_995_, v___x_1024_);
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = l_Lean_Syntax_getArg(v_x_995_, v___x_1044_);
lean_dec(v_x_995_);
v___x_1046_ = l_Lean_Syntax_isNone(v___x_1045_);
if (v___x_1046_ == 0)
{
uint8_t v___x_1047_; 
lean_inc(v___x_1045_);
v___x_1047_ = l_Lean_Syntax_matchesNull(v___x_1045_, v___x_1044_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v___x_1045_);
lean_dec(v_grindTk_1025_);
v___x_1048_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v_a_997_);
return v___x_1049_;
}
else
{
lean_object* v_mod_x3f_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_mod_x3f_1050_ = l_Lean_Syntax_getArg(v___x_1045_, v___x_1024_);
lean_dec(v___x_1045_);
v___x_1051_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_mod_x3f_1050_);
v___x_1052_ = l_Lean_Syntax_isOfKind(v_mod_x3f_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v_mod_x3f_1050_);
lean_dec(v_grindTk_1025_);
v___x_1053_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_a_997_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_mod_x3f_1050_);
v_mod_x3f_1027_ = v___x_1055_;
v___y_1028_ = v_a_996_;
v___y_1029_ = v_a_997_;
goto v___jp_1026_;
}
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v___x_1045_);
v___x_1056_ = lean_box(0);
v_mod_x3f_1027_ = v___x_1056_;
v___y_1028_ = v_a_996_;
v___y_1029_ = v_a_997_;
goto v___jp_1026_;
}
v___jp_1026_:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Fmt_fmt(v_grindTk_1025_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1030_) == 0)
{
if (lean_obj_tag(v_mod_x3f_1027_) == 0)
{
lean_object* v_a_1031_; lean_object* v_a_1032_; lean_object* v___x_1033_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
v_a_1032_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1030_, 2);
v___x_1033_ = lean_box(0);
v___y_1001_ = v___y_1028_;
v___y_1002_ = v_a_1032_;
v___y_1003_ = v_a_1031_;
v___y_1004_ = v___x_1033_;
goto v___jp_1000_;
}
else
{
lean_object* v_a_1034_; lean_object* v_a_1035_; lean_object* v_val_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1034_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1034_);
v_a_1035_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1030_, 2);
v_val_1036_ = lean_ctor_get(v_mod_x3f_1027_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_mod_x3f_1027_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v_mod_x3f_1027_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_val_1036_);
lean_dec(v_mod_x3f_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_val_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
v___y_1001_ = v___y_1028_;
v___y_1002_ = v_a_1035_;
v___y_1003_ = v_a_1034_;
v___y_1004_ = v___x_1041_;
goto v___jp_1000_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_1027_);
return v___x_1030_;
}
}
}
v___jp_1000_:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Fmt_fmt_x3f(v___y_1004_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1021_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_a_1007_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1021_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1021_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1011_ = lean_unsigned_to_nat(2u);
v___x_1012_ = lean_mk_empty_array_with_capacity(v___x_1011_);
v___x_1013_ = lean_array_push(v___x_1012_, v___y_1003_);
v___x_1014_ = lean_array_push(v___x_1013_, v_a_1006_);
v___x_1015_ = 0;
v___x_1016_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1016_, 0, v___x_999_);
lean_ctor_set_uint8(v___x_1016_, 1, v___x_1015_);
lean_ctor_set_uint8(v___x_1016_, 2, v___x_1015_);
lean_ctor_set_uint8(v___x_1016_, 3, v___x_1015_);
v___x_1017_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1014_, v___x_1016_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1017_);
v___x_1019_ = v___x_1009_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_a_1007_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_dec_ref(v___y_1003_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindQuestionAttr___boxed(lean_object* v_x_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Fmt_fmtGrindQuestionAttr(v_x_1057_, v_a_1058_, v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1(){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1067_ = l_Lean_Fmt_fmtAttribute;
v___x_1068_ = ((lean_object*)(l_Lean_Fmt_fmtGrindQuestionAttr___closed__1));
v___x_1069_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___closed__1));
v___x_1070_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindQuestionAttr___boxed), 3, 0);
v___x_1071_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1067_, v___x_1068_, v___x_1069_, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1___boxed(lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1();
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBangQuestionAttr(lean_object* v_x_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; 
v___x_1083_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1));
lean_inc(v_x_1080_);
v___x_1084_ = l_Lean_Syntax_isOfKind(v_x_1080_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v_x_1080_);
v___x_1107_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v_a_1082_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; lean_object* v_grindTk_1110_; lean_object* v_mod_x3f_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v_grindTk_1110_ = l_Lean_Syntax_getArg(v_x_1080_, v___x_1109_);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = l_Lean_Syntax_getArg(v_x_1080_, v___x_1129_);
lean_dec(v_x_1080_);
v___x_1131_ = l_Lean_Syntax_isNone(v___x_1130_);
if (v___x_1131_ == 0)
{
uint8_t v___x_1132_; 
lean_inc(v___x_1130_);
v___x_1132_ = l_Lean_Syntax_matchesNull(v___x_1130_, v___x_1129_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v___x_1130_);
lean_dec(v_grindTk_1110_);
v___x_1133_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_a_1082_);
return v___x_1134_;
}
else
{
lean_object* v_mod_x3f_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_mod_x3f_1135_ = l_Lean_Syntax_getArg(v___x_1130_, v___x_1109_);
lean_dec(v___x_1130_);
v___x_1136_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_mod_x3f_1135_);
v___x_1137_ = l_Lean_Syntax_isOfKind(v_mod_x3f_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_mod_x3f_1135_);
lean_dec(v_grindTk_1110_);
v___x_1138_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v_a_1082_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_mod_x3f_1135_);
v_mod_x3f_1112_ = v___x_1140_;
v___y_1113_ = v_a_1081_;
v___y_1114_ = v_a_1082_;
goto v___jp_1111_;
}
}
}
else
{
lean_object* v___x_1141_; 
lean_dec(v___x_1130_);
v___x_1141_ = lean_box(0);
v_mod_x3f_1112_ = v___x_1141_;
v___y_1113_ = v_a_1081_;
v___y_1114_ = v_a_1082_;
goto v___jp_1111_;
}
v___jp_1111_:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Fmt_fmt(v_grindTk_1110_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
if (lean_obj_tag(v_mod_x3f_1112_) == 0)
{
lean_object* v_a_1116_; lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
v_a_1117_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1115_, 2);
v___x_1118_ = lean_box(0);
v___y_1086_ = v___y_1113_;
v___y_1087_ = v_a_1117_;
v___y_1088_ = v_a_1116_;
v___y_1089_ = v___x_1118_;
goto v___jp_1085_;
}
else
{
lean_object* v_a_1119_; lean_object* v_a_1120_; lean_object* v_val_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v_a_1119_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1119_);
v_a_1120_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1115_, 2);
v_val_1121_ = lean_ctor_get(v_mod_x3f_1112_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_mod_x3f_1112_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v_mod_x3f_1112_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_val_1121_);
lean_dec(v_mod_x3f_1112_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_val_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
v___y_1086_ = v___y_1113_;
v___y_1087_ = v_a_1120_;
v___y_1088_ = v_a_1119_;
v___y_1089_ = v___x_1126_;
goto v___jp_1085_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_1112_);
return v___x_1115_;
}
}
}
v___jp_1085_:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Fmt_fmt_x3f(v___y_1089_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1106_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_a_1092_ = lean_ctor_get(v___x_1090_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1094_ = v___x_1090_;
v_isShared_1095_ = v_isSharedCheck_1106_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1106_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1096_ = lean_unsigned_to_nat(2u);
v___x_1097_ = lean_mk_empty_array_with_capacity(v___x_1096_);
v___x_1098_ = lean_array_push(v___x_1097_, v___y_1088_);
v___x_1099_ = lean_array_push(v___x_1098_, v_a_1091_);
v___x_1100_ = 0;
v___x_1101_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1101_, 0, v___x_1084_);
lean_ctor_set_uint8(v___x_1101_, 1, v___x_1100_);
lean_ctor_set_uint8(v___x_1101_, 2, v___x_1100_);
lean_ctor_set_uint8(v___x_1101_, 3, v___x_1100_);
v___x_1102_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1099_, v___x_1101_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1102_);
v___x_1104_ = v___x_1094_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_a_1092_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_dec_ref(v___y_1088_);
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindBangQuestionAttr___boxed(lean_object* v_x_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Fmt_fmtGrindBangQuestionAttr(v_x_1142_, v_a_1143_, v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1(){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1152_ = l_Lean_Fmt_fmtAttribute;
v___x_1153_ = ((lean_object*)(l_Lean_Fmt_fmtGrindBangQuestionAttr___closed__1));
v___x_1154_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___closed__1));
v___x_1155_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindBangQuestionAttr___boxed), 3, 0);
v___x_1156_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1152_, v___x_1153_, v___x_1154_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1___boxed(lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1();
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaAttr(lean_object* v_x_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; 
v___x_1168_ = ((lean_object*)(l_Lean_Fmt_fmtLiaAttr___closed__1));
lean_inc(v_x_1165_);
v___x_1169_ = l_Lean_Syntax_isOfKind(v_x_1165_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec(v_x_1165_);
v___x_1192_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v_a_1167_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; lean_object* v_liaTk_1195_; lean_object* v_mod_x3f_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1194_ = lean_unsigned_to_nat(0u);
v_liaTk_1195_ = l_Lean_Syntax_getArg(v_x_1165_, v___x_1194_);
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = l_Lean_Syntax_getArg(v_x_1165_, v___x_1214_);
lean_dec(v_x_1165_);
v___x_1216_ = l_Lean_Syntax_isNone(v___x_1215_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; 
lean_inc(v___x_1215_);
v___x_1217_ = l_Lean_Syntax_matchesNull(v___x_1215_, v___x_1214_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v___x_1215_);
lean_dec(v_liaTk_1195_);
v___x_1218_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v_a_1167_);
return v___x_1219_;
}
else
{
lean_object* v_mod_x3f_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_mod_x3f_1220_ = l_Lean_Syntax_getArg(v___x_1215_, v___x_1194_);
lean_dec(v___x_1215_);
v___x_1221_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_mod_x3f_1220_);
v___x_1222_ = l_Lean_Syntax_isOfKind(v_mod_x3f_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec(v_mod_x3f_1220_);
lean_dec(v_liaTk_1195_);
v___x_1223_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v_a_1167_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_mod_x3f_1220_);
v_mod_x3f_1197_ = v___x_1225_;
v___y_1198_ = v_a_1166_;
v___y_1199_ = v_a_1167_;
goto v___jp_1196_;
}
}
}
else
{
lean_object* v___x_1226_; 
lean_dec(v___x_1215_);
v___x_1226_ = lean_box(0);
v_mod_x3f_1197_ = v___x_1226_;
v___y_1198_ = v_a_1166_;
v___y_1199_ = v_a_1167_;
goto v___jp_1196_;
}
v___jp_1196_:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Fmt_fmt(v_liaTk_1195_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1200_) == 0)
{
if (lean_obj_tag(v_mod_x3f_1197_) == 0)
{
lean_object* v_a_1201_; lean_object* v_a_1202_; lean_object* v___x_1203_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
v_a_1202_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1200_, 2);
v___x_1203_ = lean_box(0);
v___y_1171_ = v___y_1198_;
v___y_1172_ = v_a_1202_;
v___y_1173_ = v_a_1201_;
v___y_1174_ = v___x_1203_;
goto v___jp_1170_;
}
else
{
lean_object* v_a_1204_; lean_object* v_a_1205_; lean_object* v_val_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1204_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1204_);
v_a_1205_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1200_, 2);
v_val_1206_ = lean_ctor_get(v_mod_x3f_1197_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_mod_x3f_1197_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v_mod_x3f_1197_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_val_1206_);
lean_dec(v_mod_x3f_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_val_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
v___y_1171_ = v___y_1198_;
v___y_1172_ = v_a_1205_;
v___y_1173_ = v_a_1204_;
v___y_1174_ = v___x_1211_;
goto v___jp_1170_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_1197_);
return v___x_1200_;
}
}
}
v___jp_1170_:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Fmt_fmt_x3f(v___y_1174_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1191_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_a_1177_ = lean_ctor_get(v___x_1175_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1179_ = v___x_1175_;
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1181_ = lean_unsigned_to_nat(2u);
v___x_1182_ = lean_mk_empty_array_with_capacity(v___x_1181_);
v___x_1183_ = lean_array_push(v___x_1182_, v___y_1173_);
v___x_1184_ = lean_array_push(v___x_1183_, v_a_1176_);
v___x_1185_ = 0;
v___x_1186_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1186_, 0, v___x_1169_);
lean_ctor_set_uint8(v___x_1186_, 1, v___x_1185_);
lean_ctor_set_uint8(v___x_1186_, 2, v___x_1185_);
lean_ctor_set_uint8(v___x_1186_, 3, v___x_1185_);
v___x_1187_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1184_, v___x_1186_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1187_);
v___x_1189_ = v___x_1179_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_a_1177_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_dec_ref(v___y_1173_);
return v___x_1175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaAttr___boxed(lean_object* v_x_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Fmt_fmtLiaAttr(v_x_1227_, v_a_1228_, v_a_1229_);
lean_dec_ref(v_a_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1(){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1237_ = l_Lean_Fmt_fmtAttribute;
v___x_1238_ = ((lean_object*)(l_Lean_Fmt_fmtLiaAttr___closed__1));
v___x_1239_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___closed__1));
v___x_1240_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLiaAttr___boxed), 3, 0);
v___x_1241_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1237_, v___x_1238_, v___x_1239_, v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1___boxed(lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1();
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaBangAttr(lean_object* v_x_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1253_; uint8_t v___x_1254_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; 
v___x_1253_ = ((lean_object*)(l_Lean_Fmt_fmtLiaBangAttr___closed__1));
lean_inc(v_x_1250_);
v___x_1254_ = l_Lean_Syntax_isOfKind(v_x_1250_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v_x_1250_);
v___x_1277_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v_a_1252_);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; lean_object* v_liaTk_1280_; lean_object* v_mod_x3f_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v_liaTk_1280_ = l_Lean_Syntax_getArg(v_x_1250_, v___x_1279_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = l_Lean_Syntax_getArg(v_x_1250_, v___x_1299_);
lean_dec(v_x_1250_);
v___x_1301_ = l_Lean_Syntax_isNone(v___x_1300_);
if (v___x_1301_ == 0)
{
uint8_t v___x_1302_; 
lean_inc(v___x_1300_);
v___x_1302_ = l_Lean_Syntax_matchesNull(v___x_1300_, v___x_1299_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v___x_1300_);
lean_dec(v_liaTk_1280_);
v___x_1303_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_a_1252_);
return v___x_1304_;
}
else
{
lean_object* v_mod_x3f_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_mod_x3f_1305_ = l_Lean_Syntax_getArg(v___x_1300_, v___x_1279_);
lean_dec(v___x_1300_);
v___x_1306_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_mod_x3f_1305_);
v___x_1307_ = l_Lean_Syntax_isOfKind(v_mod_x3f_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v_mod_x3f_1305_);
lean_dec(v_liaTk_1280_);
v___x_1308_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_a_1252_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v_mod_x3f_1305_);
v_mod_x3f_1282_ = v___x_1310_;
v___y_1283_ = v_a_1251_;
v___y_1284_ = v_a_1252_;
goto v___jp_1281_;
}
}
}
else
{
lean_object* v___x_1311_; 
lean_dec(v___x_1300_);
v___x_1311_ = lean_box(0);
v_mod_x3f_1282_ = v___x_1311_;
v___y_1283_ = v_a_1251_;
v___y_1284_ = v_a_1252_;
goto v___jp_1281_;
}
v___jp_1281_:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Fmt_fmt(v_liaTk_1280_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
if (lean_obj_tag(v_mod_x3f_1282_) == 0)
{
lean_object* v_a_1286_; lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
v_a_1287_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1285_, 2);
v___x_1288_ = lean_box(0);
v___y_1256_ = v___y_1283_;
v___y_1257_ = v_a_1286_;
v___y_1258_ = v_a_1287_;
v___y_1259_ = v___x_1288_;
goto v___jp_1255_;
}
else
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1289_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1289_);
v_a_1290_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1285_, 2);
v_val_1291_ = lean_ctor_get(v_mod_x3f_1282_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_mod_x3f_1282_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v_mod_x3f_1282_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v_mod_x3f_1282_);
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
v___y_1256_ = v___y_1283_;
v___y_1257_ = v_a_1289_;
v___y_1258_ = v_a_1290_;
v___y_1259_ = v___x_1296_;
goto v___jp_1255_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_1282_);
return v___x_1285_;
}
}
}
v___jp_1255_:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Fmt_fmt_x3f(v___y_1259_, v___y_1256_, v___y_1258_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1276_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_a_1262_ = lean_ctor_get(v___x_1260_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1264_ = v___x_1260_;
v_isShared_1265_ = v_isSharedCheck_1276_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1276_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1266_ = lean_unsigned_to_nat(2u);
v___x_1267_ = lean_mk_empty_array_with_capacity(v___x_1266_);
v___x_1268_ = lean_array_push(v___x_1267_, v___y_1257_);
v___x_1269_ = lean_array_push(v___x_1268_, v_a_1261_);
v___x_1270_ = 0;
v___x_1271_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1271_, 0, v___x_1254_);
lean_ctor_set_uint8(v___x_1271_, 1, v___x_1270_);
lean_ctor_set_uint8(v___x_1271_, 2, v___x_1270_);
lean_ctor_set_uint8(v___x_1271_, 3, v___x_1270_);
v___x_1272_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1269_, v___x_1271_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1272_);
v___x_1274_ = v___x_1264_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_a_1262_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_dec_ref(v___y_1257_);
return v___x_1260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaBangAttr___boxed(lean_object* v_x_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Fmt_fmtLiaBangAttr(v_x_1312_, v_a_1313_, v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1(){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1322_ = l_Lean_Fmt_fmtAttribute;
v___x_1323_ = ((lean_object*)(l_Lean_Fmt_fmtLiaBangAttr___closed__1));
v___x_1324_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___closed__1));
v___x_1325_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLiaBangAttr___boxed), 3, 0);
v___x_1326_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1322_, v___x_1323_, v___x_1324_, v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1___boxed(lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1();
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaQuestionAttr(lean_object* v_x_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; 
v___x_1338_ = ((lean_object*)(l_Lean_Fmt_fmtLiaQuestionAttr___closed__1));
lean_inc(v_x_1335_);
v___x_1339_ = l_Lean_Syntax_isOfKind(v_x_1335_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec(v_x_1335_);
v___x_1362_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v_a_1337_);
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; lean_object* v_liaTk_1365_; lean_object* v_mod_x3f_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1364_ = lean_unsigned_to_nat(0u);
v_liaTk_1365_ = l_Lean_Syntax_getArg(v_x_1335_, v___x_1364_);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = l_Lean_Syntax_getArg(v_x_1335_, v___x_1384_);
lean_dec(v_x_1335_);
v___x_1386_ = l_Lean_Syntax_isNone(v___x_1385_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1387_; 
lean_inc(v___x_1385_);
v___x_1387_ = l_Lean_Syntax_matchesNull(v___x_1385_, v___x_1384_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v___x_1385_);
lean_dec(v_liaTk_1365_);
v___x_1388_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v_a_1337_);
return v___x_1389_;
}
else
{
lean_object* v_mod_x3f_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_mod_x3f_1390_ = l_Lean_Syntax_getArg(v___x_1385_, v___x_1364_);
lean_dec(v___x_1385_);
v___x_1391_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_mod_x3f_1390_);
v___x_1392_ = l_Lean_Syntax_isOfKind(v_mod_x3f_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec(v_mod_x3f_1390_);
lean_dec(v_liaTk_1365_);
v___x_1393_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
lean_ctor_set(v___x_1394_, 1, v_a_1337_);
return v___x_1394_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_mod_x3f_1390_);
v_mod_x3f_1367_ = v___x_1395_;
v___y_1368_ = v_a_1336_;
v___y_1369_ = v_a_1337_;
goto v___jp_1366_;
}
}
}
else
{
lean_object* v___x_1396_; 
lean_dec(v___x_1385_);
v___x_1396_ = lean_box(0);
v_mod_x3f_1367_ = v___x_1396_;
v___y_1368_ = v_a_1336_;
v___y_1369_ = v_a_1337_;
goto v___jp_1366_;
}
v___jp_1366_:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Fmt_fmt(v_liaTk_1365_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1370_) == 0)
{
if (lean_obj_tag(v_mod_x3f_1367_) == 0)
{
lean_object* v_a_1371_; lean_object* v_a_1372_; lean_object* v___x_1373_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
v_a_1372_ = lean_ctor_get(v___x_1370_, 1);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1370_, 2);
v___x_1373_ = lean_box(0);
v___y_1341_ = v_a_1371_;
v___y_1342_ = v_a_1372_;
v___y_1343_ = v___y_1368_;
v___y_1344_ = v___x_1373_;
goto v___jp_1340_;
}
else
{
lean_object* v_a_1374_; lean_object* v_a_1375_; lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1374_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1374_);
v_a_1375_ = lean_ctor_get(v___x_1370_, 1);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1370_, 2);
v_val_1376_ = lean_ctor_get(v_mod_x3f_1367_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_mod_x3f_1367_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v_mod_x3f_1367_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_dec(v_mod_x3f_1367_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_val_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
v___y_1341_ = v_a_1374_;
v___y_1342_ = v_a_1375_;
v___y_1343_ = v___y_1368_;
v___y_1344_ = v___x_1381_;
goto v___jp_1340_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_1367_);
return v___x_1370_;
}
}
}
v___jp_1340_:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_Fmt_fmt_x3f(v___y_1344_, v___y_1343_, v___y_1342_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1361_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_a_1347_ = lean_ctor_get(v___x_1345_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1349_ = v___x_1345_;
v_isShared_1350_ = v_isSharedCheck_1361_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1361_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1351_ = lean_unsigned_to_nat(2u);
v___x_1352_ = lean_mk_empty_array_with_capacity(v___x_1351_);
v___x_1353_ = lean_array_push(v___x_1352_, v___y_1341_);
v___x_1354_ = lean_array_push(v___x_1353_, v_a_1346_);
v___x_1355_ = 0;
v___x_1356_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1356_, 0, v___x_1339_);
lean_ctor_set_uint8(v___x_1356_, 1, v___x_1355_);
lean_ctor_set_uint8(v___x_1356_, 2, v___x_1355_);
lean_ctor_set_uint8(v___x_1356_, 3, v___x_1355_);
v___x_1357_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1354_, v___x_1356_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1357_);
v___x_1359_ = v___x_1349_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_a_1347_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_dec_ref(v___y_1341_);
return v___x_1345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaQuestionAttr___boxed(lean_object* v_x_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Fmt_fmtLiaQuestionAttr(v_x_1397_, v_a_1398_, v_a_1399_);
lean_dec_ref(v_a_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1(){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1407_ = l_Lean_Fmt_fmtAttribute;
v___x_1408_ = ((lean_object*)(l_Lean_Fmt_fmtLiaQuestionAttr___closed__1));
v___x_1409_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___closed__1));
v___x_1410_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLiaQuestionAttr___boxed), 3, 0);
v___x_1411_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1407_, v___x_1408_, v___x_1409_, v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1___boxed(lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1();
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaBangQuestionAttr(lean_object* v_x_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; 
v___x_1423_ = ((lean_object*)(l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1));
lean_inc(v_x_1420_);
v___x_1424_ = l_Lean_Syntax_isOfKind(v_x_1420_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v_x_1420_);
v___x_1447_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v_a_1422_);
return v___x_1448_;
}
else
{
lean_object* v___x_1449_; lean_object* v_liaTk_1450_; lean_object* v_mod_x3f_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v_liaTk_1450_ = l_Lean_Syntax_getArg(v_x_1420_, v___x_1449_);
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = l_Lean_Syntax_getArg(v_x_1420_, v___x_1469_);
lean_dec(v_x_1420_);
v___x_1471_ = l_Lean_Syntax_isNone(v___x_1470_);
if (v___x_1471_ == 0)
{
uint8_t v___x_1472_; 
lean_inc(v___x_1470_);
v___x_1472_ = l_Lean_Syntax_matchesNull(v___x_1470_, v___x_1469_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec(v___x_1470_);
lean_dec(v_liaTk_1450_);
v___x_1473_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v_a_1422_);
return v___x_1474_;
}
else
{
lean_object* v_mod_x3f_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v_mod_x3f_1475_ = l_Lean_Syntax_getArg(v___x_1470_, v___x_1449_);
lean_dec(v___x_1470_);
v___x_1476_ = ((lean_object*)(l_Lean_Fmt_fmtGrindMod___closed__1));
lean_inc(v_mod_x3f_1475_);
v___x_1477_ = l_Lean_Syntax_isOfKind(v_mod_x3f_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v_mod_x3f_1475_);
lean_dec(v_liaTk_1450_);
v___x_1478_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v_a_1422_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_mod_x3f_1475_);
v_mod_x3f_1452_ = v___x_1480_;
v___y_1453_ = v_a_1421_;
v___y_1454_ = v_a_1422_;
goto v___jp_1451_;
}
}
}
else
{
lean_object* v___x_1481_; 
lean_dec(v___x_1470_);
v___x_1481_ = lean_box(0);
v_mod_x3f_1452_ = v___x_1481_;
v___y_1453_ = v_a_1421_;
v___y_1454_ = v_a_1422_;
goto v___jp_1451_;
}
v___jp_1451_:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Fmt_fmt(v_liaTk_1450_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1455_) == 0)
{
if (lean_obj_tag(v_mod_x3f_1452_) == 0)
{
lean_object* v_a_1456_; lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
v_a_1457_ = lean_ctor_get(v___x_1455_, 1);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1455_, 2);
v___x_1458_ = lean_box(0);
v___y_1426_ = v_a_1457_;
v___y_1427_ = v_a_1456_;
v___y_1428_ = v___y_1453_;
v___y_1429_ = v___x_1458_;
goto v___jp_1425_;
}
else
{
lean_object* v_a_1459_; lean_object* v_a_1460_; lean_object* v_val_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1459_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1459_);
v_a_1460_ = lean_ctor_get(v___x_1455_, 1);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1455_, 2);
v_val_1461_ = lean_ctor_get(v_mod_x3f_1452_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_mod_x3f_1452_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v_mod_x3f_1452_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_val_1461_);
lean_dec(v_mod_x3f_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_val_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
v___y_1426_ = v_a_1460_;
v___y_1427_ = v_a_1459_;
v___y_1428_ = v___y_1453_;
v___y_1429_ = v___x_1466_;
goto v___jp_1425_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_1452_);
return v___x_1455_;
}
}
}
v___jp_1425_:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Fmt_fmt_x3f(v___y_1429_, v___y_1428_, v___y_1426_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1446_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_a_1432_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1434_ = v___x_1430_;
v_isShared_1435_ = v_isSharedCheck_1446_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1446_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1436_ = lean_unsigned_to_nat(2u);
v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
v___x_1438_ = lean_array_push(v___x_1437_, v___y_1427_);
v___x_1439_ = lean_array_push(v___x_1438_, v_a_1431_);
v___x_1440_ = 0;
v___x_1441_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1441_, 0, v___x_1424_);
lean_ctor_set_uint8(v___x_1441_, 1, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, 2, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, 3, v___x_1440_);
v___x_1442_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1439_, v___x_1441_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1442_);
v___x_1444_ = v___x_1434_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_a_1432_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_dec_ref(v___y_1427_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaBangQuestionAttr___boxed(lean_object* v_x_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Fmt_fmtLiaBangQuestionAttr(v_x_1482_, v_a_1483_, v_a_1484_);
lean_dec_ref(v_a_1483_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1(){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1492_ = l_Lean_Fmt_fmtAttribute;
v___x_1493_ = ((lean_object*)(l_Lean_Fmt_fmtLiaBangQuestionAttr___closed__1));
v___x_1494_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___closed__1));
v___x_1495_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLiaBangQuestionAttr___boxed), 3, 0);
v___x_1496_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1492_, v___x_1493_, v___x_1494_, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1___boxed(lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1();
return v_res_1498_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Attr(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEq___regBuiltin_Lean_Fmt_fmtGrindEq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqRhs___regBuiltin_Lean_Fmt_fmtGrindEqRhs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBoth___regBuiltin_Lean_Fmt_fmtGrindEqBoth__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindEqBwd___regBuiltin_Lean_Fmt_fmtGrindEqBwd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBwd___regBuiltin_Lean_Fmt_fmtGrindBwd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindDef___regBuiltin_Lean_Fmt_fmtGrindDef__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindCasesEager___regBuiltin_Lean_Fmt_fmtGrindCasesEager__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindHomFallback___regBuiltin_Lean_Fmt_fmtGrindHomFallback__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindNorm___regBuiltin_Lean_Fmt_fmtGrindNorm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindSym___regBuiltin_Lean_Fmt_fmtGrindSym__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindMod___regBuiltin_Lean_Fmt_fmtGrindMod__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindAttr___regBuiltin_Lean_Fmt_fmtGrindAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangAttr___regBuiltin_Lean_Fmt_fmtGrindBangAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindQuestionAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtGrindBangQuestionAttr___regBuiltin_Lean_Fmt_fmtGrindBangQuestionAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaAttr___regBuiltin_Lean_Fmt_fmtLiaAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangAttr___regBuiltin_Lean_Fmt_fmtLiaBangAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaQuestionAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Attr_0__Lean_Fmt_fmtLiaBangQuestionAttr___regBuiltin_Lean_Fmt_fmtLiaBangQuestionAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Attr(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Attr(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
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
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Grind_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
