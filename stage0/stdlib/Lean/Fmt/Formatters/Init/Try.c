// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Try
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Try import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmtAltsTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_tacticOptConfigItems___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryTrace_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTryTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtTryTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtTryTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtTryTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtTryTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtTryTrace___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtTryTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tryTrace"};
static const lean_object* l_Lean_Fmt_fmtTryTrace___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtTryTrace___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTrace___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTrace___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(222, 128, 230, 128, 87, 180, 97, 21)}};
static const lean_object* l_Lean_Fmt_fmtTryTrace___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtTryTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Fmt_fmtTryTrace___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtTryTrace___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTrace___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTrace___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Fmt_fmtTryTrace___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtTryTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(60, 92, 240, 64, 170, 15, 118, 63)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTryTraceWith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tryTraceWith"};
static const lean_object* l_Lean_Fmt_fmtTryTraceWith___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTryTraceWith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTraceWith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTraceWith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTraceWith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 89, 220, 7, 252, 66, 194, 105)}};
static const lean_object* l_Lean_Fmt_fmtTryTraceWith___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtTryTraceWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Fmt_fmtTryTraceWith___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtTryTraceWith___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTraceWith___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTraceWith___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryTraceWith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Fmt_fmtTryTraceWith___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTryTraceWith___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryTraceWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryTraceWith___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtTryTraceWith"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 240, 66, 1, 26, 250, 42, 59)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtAttemptAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attemptAll"};
static const lean_object* l_Lean_Fmt_fmtAttemptAll___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAttemptAll___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtAttemptAll___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtAttemptAll___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAttemptAll___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtAttemptAll___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAttemptAll___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtAttemptAll___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAttemptAll___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAttemptAll___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 233, 242, 37, 159, 125, 179, 213)}};
static const lean_object* l_Lean_Fmt_fmtAttemptAll___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAttemptAll___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttemptAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttemptAll___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtAttemptAll"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 122, 157, 27, 191, 203, 238, 27)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtAttemptAllPar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "attemptAllPar"};
static const lean_object* l_Lean_Fmt_fmtAttemptAllPar___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAttemptAllPar___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtAttemptAllPar___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtAttemptAllPar___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAttemptAllPar___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtAttemptAllPar___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAttemptAllPar___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtAttemptAllPar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAttemptAllPar___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAttemptAllPar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 73, 192, 8, 247, 249, 123, 255)}};
static const lean_object* l_Lean_Fmt_fmtAttemptAllPar___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAttemptAllPar___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttemptAllPar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttemptAllPar___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtAttemptAllPar"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 18, 184, 109, 35, 28, 13, 198)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtFirstPar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "firstPar"};
static const lean_object* l_Lean_Fmt_fmtFirstPar___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtFirstPar___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtFirstPar___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtFirstPar___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtFirstPar___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtFirstPar___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtFirstPar___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtFirstPar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtFirstPar___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtFirstPar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 43, 83, 229, 83, 112, 229, 7)}};
static const lean_object* l_Lean_Fmt_fmtFirstPar___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtFirstPar___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFirstPar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFirstPar___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtFirstPar"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 228, 53, 195, 255, 245, 101, 231)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTryResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tryResult"};
static const lean_object* l_Lean_Fmt_fmtTryResult___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTryResult___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTryResult___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryResult___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryResult___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryResult___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryResult___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryResult___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryResult___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTryResult___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 153, 96, 187, 124, 208, 140, 174)}};
static const lean_object* l_Lean_Fmt_fmtTryResult___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTryResult___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryResult___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtTryResult"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 246, 74, 33, 110, 184, 19, 159)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterTryTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtRegisterTryTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterTryTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "registerTryTactic"};
static const lean_object* l_Lean_Fmt_fmtRegisterTryTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 133, 180, 171, 152, 84, 222, 30)}};
static const lean_object* l_Lean_Fmt_fmtRegisterTryTactic___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__2_value;
static const lean_array_object l_Lean_Fmt_fmtRegisterTryTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtRegisterTryTactic___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterTryTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtRegisterTryTactic___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtRegisterTryTactic___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterTryTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtRegisterTryTactic___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__7_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__7_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterTryTactic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__7_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtRegisterTryTactic___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtRegisterTryTactic___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterTryTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterTryTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtRegisterTryTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 206, 98, 108, 88, 222, 60, 160)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryTrace_spec__0(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_usize_dec_lt(v_i_2_, v_sz_1_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_bs_3_);
lean_ctor_set(v___x_7_, 1, v___y_5_);
return v___x_7_;
}
else
{
lean_object* v_v_8_; lean_object* v___x_9_; 
v_v_8_ = lean_array_uget_borrowed(v_bs_3_, v_i_2_);
lean_inc(v_v_8_);
v___x_9_ = l_Lean_Fmt_fmt(v_v_8_, v___y_4_, v___y_5_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v_a_11_; lean_object* v___x_12_; lean_object* v_bs_x27_13_; size_t v___x_14_; size_t v___x_15_; lean_object* v___x_16_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
v_a_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_a_11_);
lean_dec_ref_known(v___x_9_, 2);
v___x_12_ = lean_unsigned_to_nat(0u);
v_bs_x27_13_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_12_);
v___x_14_ = ((size_t)1ULL);
v___x_15_ = lean_usize_add(v_i_2_, v___x_14_);
v___x_16_ = lean_array_uset(v_bs_x27_13_, v_i_2_, v_a_10_);
v_i_2_ = v___x_15_;
v_bs_3_ = v___x_16_;
v___y_5_ = v_a_11_;
goto _start;
}
else
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_26_; 
lean_dec_ref(v_bs_3_);
v_a_18_ = lean_ctor_get(v___x_9_, 0);
v_a_19_ = lean_ctor_get(v___x_9_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_26_ == 0)
{
v___x_21_ = v___x_9_;
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_inc(v_a_18_);
lean_dec(v___x_9_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_a_18_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_a_19_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryTrace_spec__0___boxed(lean_object* v_sz_27_, lean_object* v_i_28_, lean_object* v_bs_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
size_t v_sz_boxed_32_; size_t v_i_boxed_33_; lean_object* v_res_34_; 
v_sz_boxed_32_ = lean_unbox_usize(v_sz_27_);
lean_dec(v_sz_27_);
v_i_boxed_33_ = lean_unbox_usize(v_i_28_);
lean_dec(v_i_28_);
v_res_34_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryTrace_spec__0(v_sz_boxed_32_, v_i_boxed_33_, v_bs_29_, v___y_30_, v___y_31_);
lean_dec_ref(v___y_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryTrace(lean_object* v_x_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = ((lean_object*)(l_Lean_Fmt_fmtTryTrace___closed__4));
lean_inc(v_x_50_);
v___x_54_ = l_Lean_Syntax_isOfKind(v_x_50_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_x_50_);
v___x_55_ = l_Lean_Fmt_Error_partialFormatter;
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v_a_52_);
return v___x_56_;
}
else
{
lean_object* v___x_57_; lean_object* v_cfg_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_57_ = lean_unsigned_to_nat(1u);
v_cfg_58_ = l_Lean_Syntax_getArg(v_x_50_, v___x_57_);
v___x_59_ = ((lean_object*)(l_Lean_Fmt_fmtTryTrace___closed__6));
lean_inc(v_cfg_58_);
v___x_60_ = l_Lean_Syntax_isOfKind(v_cfg_58_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_cfg_58_);
lean_dec(v_x_50_);
v___x_61_ = l_Lean_Fmt_Error_partialFormatter;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v_a_52_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; lean_object* v_tryTk_64_; lean_object* v___x_65_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v_tryTk_64_ = l_Lean_Syntax_getArg(v_x_50_, v___x_63_);
lean_dec(v_x_50_);
v___x_65_ = l_Lean_Fmt_fmt(v_tryTk_64_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v_a_67_; lean_object* v___x_68_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
v_a_67_ = lean_ctor_get(v___x_65_, 1);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_65_, 2);
v___x_68_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_58_, v_a_67_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v_a_70_; size_t v_sz_71_; size_t v___x_72_; lean_object* v___x_73_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
v_a_70_ = lean_ctor_get(v___x_68_, 1);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_68_, 2);
v_sz_71_ = lean_array_size(v_a_69_);
v___x_72_ = ((size_t)0ULL);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryTrace_spec__0(v_sz_71_, v___x_72_, v_a_69_, v_a_51_, v_a_70_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_88_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_a_75_ = lean_ctor_get(v___x_73_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_88_ == 0)
{
v___x_77_ = v___x_73_;
v_isShared_78_ = v_isSharedCheck_88_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_88_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_79_ = lean_mk_empty_array_with_capacity(v___x_57_);
v___x_80_ = lean_array_push(v___x_79_, v_a_66_);
v___x_81_ = l_Array_append___redArg(v___x_80_, v_a_74_);
lean_dec(v_a_74_);
v___x_82_ = 0;
v___x_83_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_83_, 0, v___x_60_);
lean_ctor_set_uint8(v___x_83_, 1, v___x_82_);
lean_ctor_set_uint8(v___x_83_, 2, v___x_82_);
lean_ctor_set_uint8(v___x_83_, 3, v___x_82_);
v___x_84_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_81_, v___x_83_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_84_);
v___x_86_ = v___x_77_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_a_75_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
else
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
lean_dec(v_a_66_);
v_a_89_ = lean_ctor_get(v___x_73_, 0);
v_a_90_ = lean_ctor_get(v___x_73_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_73_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_inc(v_a_89_);
lean_dec(v___x_73_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_89_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_object* v_a_98_; lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec(v_a_66_);
v_a_98_ = lean_ctor_get(v___x_68_, 0);
v_a_99_ = lean_ctor_get(v___x_68_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_68_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_inc(v_a_98_);
lean_dec(v___x_68_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_98_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
else
{
lean_dec(v_cfg_58_);
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryTrace___boxed(lean_object* v_x_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Fmt_fmtTryTrace(v_x_107_, v_a_108_, v_a_109_);
lean_dec_ref(v_a_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1(){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = l_Lean_Fmt_fmtAttribute;
v___x_119_ = ((lean_object*)(l_Lean_Fmt_fmtTryTrace___closed__4));
v___x_120_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___closed__2));
v___x_121_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTryTrace___boxed), 3, 0);
v___x_122_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_118_, v___x_119_, v___x_120_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1___boxed(lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1();
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryTraceWith(lean_object* v_x_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Fmt_fmtTryTraceWith___closed__1));
lean_inc(v_x_137_);
v___x_141_ = l_Lean_Syntax_isOfKind(v_x_137_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_x_137_);
v___x_142_ = l_Lean_Fmt_Error_partialFormatter;
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_139_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; lean_object* v_cfg_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v_cfg_145_ = l_Lean_Syntax_getArg(v_x_137_, v___x_144_);
v___x_146_ = ((lean_object*)(l_Lean_Fmt_fmtTryTrace___closed__6));
lean_inc(v_cfg_145_);
v___x_147_ = l_Lean_Syntax_isOfKind(v_cfg_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_cfg_145_);
lean_dec(v_x_137_);
v___x_148_ = l_Lean_Fmt_Error_partialFormatter;
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_a_139_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(3u);
v___x_151_ = l_Lean_Syntax_getArg(v_x_137_, v___x_150_);
v___x_152_ = ((lean_object*)(l_Lean_Fmt_fmtTryTraceWith___closed__3));
lean_inc(v___x_151_);
v___x_153_ = l_Lean_Syntax_isOfKind(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_151_);
lean_dec(v_cfg_145_);
lean_dec(v_x_137_);
v___x_154_ = l_Lean_Fmt_Error_partialFormatter;
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_139_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v_tryTk_157_; lean_object* v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v_tryTk_157_ = l_Lean_Syntax_getArg(v_x_137_, v___x_156_);
v___x_158_ = l_Lean_Fmt_fmt(v_tryTk_157_, v_a_138_, v_a_139_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v_a_160_; lean_object* v___x_161_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
v_a_160_ = lean_ctor_get(v___x_158_, 1);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_158_, 2);
v___x_161_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_145_, v_a_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v_a_163_; size_t v_sz_164_; size_t v___x_165_; lean_object* v___x_166_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
v_a_163_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_161_, 2);
v_sz_164_ = lean_array_size(v_a_162_);
v___x_165_ = ((size_t)0ULL);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryTrace_spec__0(v_sz_164_, v___x_165_, v_a_162_, v_a_138_, v_a_163_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v_arrowTk_170_; lean_object* v___x_171_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
v_a_168_ = lean_ctor_get(v___x_166_, 1);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_166_, 2);
v___x_169_ = lean_unsigned_to_nat(2u);
v_arrowTk_170_ = l_Lean_Syntax_getArg(v_x_137_, v___x_169_);
lean_dec(v_x_137_);
v___x_171_ = l_Lean_Fmt_fmt(v_arrowTk_170_, v_a_138_, v_a_168_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v_a_173_; lean_object* v___x_174_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
v_a_173_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_171_, 2);
v___x_174_ = l_Lean_Fmt_fmt(v___x_151_, v_a_138_, v_a_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_190_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_a_176_ = lean_ctor_get(v___x_174_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_190_ == 0)
{
v___x_178_ = v___x_174_;
v_isShared_179_ = v_isSharedCheck_190_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_190_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_144_);
v___x_181_ = lean_array_push(v___x_180_, v_a_159_);
v___x_182_ = l_Array_append___redArg(v___x_181_, v_a_167_);
lean_dec(v_a_167_);
v___x_183_ = 0;
v___x_184_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_184_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_184_, 1, v___x_183_);
lean_ctor_set_uint8(v___x_184_, 2, v___x_183_);
lean_ctor_set_uint8(v___x_184_, 3, v___x_183_);
v___x_185_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_182_, v___x_184_);
v___x_186_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_185_, v_a_172_, v_a_175_, v___x_183_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_186_);
v___x_188_ = v___x_178_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_a_176_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_dec(v_a_172_);
lean_dec(v_a_167_);
lean_dec(v_a_159_);
return v___x_174_;
}
}
else
{
lean_dec(v_a_167_);
lean_dec(v_a_159_);
lean_dec(v___x_151_);
return v___x_171_;
}
}
else
{
lean_object* v_a_191_; lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v_a_159_);
lean_dec(v___x_151_);
lean_dec(v_x_137_);
v_a_191_ = lean_ctor_get(v___x_166_, 0);
v_a_192_ = lean_ctor_get(v___x_166_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_166_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_inc(v_a_191_);
lean_dec(v___x_166_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_a_159_);
lean_dec(v___x_151_);
lean_dec(v_x_137_);
v_a_200_ = lean_ctor_get(v___x_161_, 0);
v_a_201_ = lean_ctor_get(v___x_161_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_161_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_inc(v_a_200_);
lean_dec(v___x_161_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_200_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_dec(v___x_151_);
lean_dec(v_cfg_145_);
lean_dec(v_x_137_);
return v___x_158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryTraceWith___boxed(lean_object* v_x_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Fmt_fmtTryTraceWith(v_x_209_, v_a_210_, v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1(){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_219_ = l_Lean_Fmt_fmtAttribute;
v___x_220_ = ((lean_object*)(l_Lean_Fmt_fmtTryTraceWith___closed__1));
v___x_221_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___closed__1));
v___x_222_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTryTraceWith___boxed), 3, 0);
v___x_223_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_219_, v___x_220_, v___x_221_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1___boxed(lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1();
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__1(size_t v_sz_226_, size_t v_i_227_, lean_object* v_bs_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = lean_usize_dec_lt(v_i_227_, v_sz_226_);
if (v___x_229_ == 0)
{
return v_bs_228_;
}
else
{
lean_object* v_v_230_; lean_object* v_snd_231_; lean_object* v___x_232_; lean_object* v_bs_x27_233_; size_t v___x_234_; size_t v___x_235_; lean_object* v___x_236_; 
v_v_230_ = lean_array_uget_borrowed(v_bs_228_, v_i_227_);
v_snd_231_ = lean_ctor_get(v_v_230_, 1);
lean_inc(v_snd_231_);
v___x_232_ = lean_unsigned_to_nat(0u);
v_bs_x27_233_ = lean_array_uset(v_bs_228_, v_i_227_, v___x_232_);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_227_, v___x_234_);
v___x_236_ = lean_array_uset(v_bs_x27_233_, v_i_227_, v_snd_231_);
v_i_227_ = v___x_235_;
v_bs_228_ = v___x_236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__1___boxed(lean_object* v_sz_238_, lean_object* v_i_239_, lean_object* v_bs_240_){
_start:
{
size_t v_sz_boxed_241_; size_t v_i_boxed_242_; lean_object* v_res_243_; 
v_sz_boxed_241_ = lean_unbox_usize(v_sz_238_);
lean_dec(v_sz_238_);
v_i_boxed_242_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__1(v_sz_boxed_241_, v_i_boxed_242_, v_bs_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__2(size_t v_sz_244_, size_t v_i_245_, lean_object* v_bs_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_lt(v_i_245_, v_sz_244_);
if (v___x_247_ == 0)
{
return v_bs_246_;
}
else
{
lean_object* v_v_248_; lean_object* v_fst_249_; lean_object* v___x_250_; lean_object* v_bs_x27_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; 
v_v_248_ = lean_array_uget_borrowed(v_bs_246_, v_i_245_);
v_fst_249_ = lean_ctor_get(v_v_248_, 0);
lean_inc(v_fst_249_);
v___x_250_ = lean_unsigned_to_nat(0u);
v_bs_x27_251_ = lean_array_uset(v_bs_246_, v_i_245_, v___x_250_);
v___x_252_ = ((size_t)1ULL);
v___x_253_ = lean_usize_add(v_i_245_, v___x_252_);
v___x_254_ = lean_array_uset(v_bs_x27_251_, v_i_245_, v_fst_249_);
v_i_245_ = v___x_253_;
v_bs_246_ = v___x_254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__2___boxed(lean_object* v_sz_256_, lean_object* v_i_257_, lean_object* v_bs_258_){
_start:
{
size_t v_sz_boxed_259_; size_t v_i_boxed_260_; lean_object* v_res_261_; 
v_sz_boxed_259_ = lean_unbox_usize(v_sz_256_);
lean_dec(v_sz_256_);
v_i_boxed_260_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__2(v_sz_boxed_259_, v_i_boxed_260_, v_bs_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0(size_t v_sz_265_, size_t v_i_266_, lean_object* v_bs_267_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_lt(v_i_266_, v_sz_265_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_bs_267_);
return v___x_269_;
}
else
{
lean_object* v_v_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_v_270_ = lean_array_uget(v_bs_267_, v_i_266_);
v___x_271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___closed__1));
lean_inc(v_v_270_);
v___x_272_ = l_Lean_Syntax_isOfKind(v_v_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec(v_v_270_);
lean_dec_ref(v_bs_267_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v_tacticSeqs_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_274_ = lean_unsigned_to_nat(1u);
v_tacticSeqs_275_ = l_Lean_Syntax_getArg(v_v_270_, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_Fmt_fmtTryTraceWith___closed__3));
lean_inc(v_tacticSeqs_275_);
v___x_277_ = l_Lean_Syntax_isOfKind(v_tacticSeqs_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec(v_tacticSeqs_275_);
lean_dec(v_v_270_);
lean_dec_ref(v_bs_267_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v_bs_x27_280_; lean_object* v_barTks_281_; lean_object* v___x_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v_bs_x27_280_ = lean_array_uset(v_bs_267_, v_i_266_, v___x_279_);
v_barTks_281_ = l_Lean_Syntax_getArg(v_v_270_, v___x_279_);
lean_dec(v_v_270_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_barTks_281_);
lean_ctor_set(v___x_282_, 1, v_tacticSeqs_275_);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_add(v_i_266_, v___x_283_);
v___x_285_ = lean_array_uset(v_bs_x27_280_, v_i_266_, v___x_282_);
v_i_266_ = v___x_284_;
v_bs_267_ = v___x_285_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0___boxed(lean_object* v_sz_287_, lean_object* v_i_288_, lean_object* v_bs_289_){
_start:
{
size_t v_sz_boxed_290_; size_t v_i_boxed_291_; lean_object* v_res_292_; 
v_sz_boxed_290_ = lean_unbox_usize(v_sz_287_);
lean_dec(v_sz_287_);
v_i_boxed_291_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0(v_sz_boxed_290_, v_i_boxed_291_, v_bs_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttemptAll(lean_object* v_x_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Fmt_fmtAttemptAll___closed__1));
lean_inc(v_x_299_);
v___x_303_ = l_Lean_Syntax_isOfKind(v_x_299_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_x_299_);
v___x_304_ = l_Lean_Fmt_Error_partialFormatter;
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_a_301_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; size_t v_sz_309_; size_t v___x_310_; lean_object* v___x_311_; 
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = l_Lean_Syntax_getArg(v_x_299_, v___x_306_);
v___x_308_ = l_Lean_Syntax_getArgs(v___x_307_);
lean_dec(v___x_307_);
v_sz_309_ = lean_array_size(v___x_308_);
v___x_310_ = ((size_t)0ULL);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0(v_sz_309_, v___x_310_, v___x_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_x_299_);
v___x_312_ = l_Lean_Fmt_Error_partialFormatter;
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_a_301_);
return v___x_313_;
}
else
{
lean_object* v_val_314_; lean_object* v___x_315_; lean_object* v_attemptAllTk_316_; size_t v_sz_317_; lean_object* v_tacticSeqs_318_; lean_object* v_barTks_319_; lean_object* v___x_320_; 
v_val_314_ = lean_ctor_get(v___x_311_, 0);
lean_inc_n(v_val_314_, 2);
lean_dec_ref_known(v___x_311_, 1);
v___x_315_ = lean_unsigned_to_nat(0u);
v_attemptAllTk_316_ = l_Lean_Syntax_getArg(v_x_299_, v___x_315_);
lean_dec(v_x_299_);
v_sz_317_ = lean_array_size(v_val_314_);
v_tacticSeqs_318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__1(v_sz_317_, v___x_310_, v_val_314_);
v_barTks_319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__2(v_sz_317_, v___x_310_, v_val_314_);
v___x_320_ = l_Lean_Fmt_fmtAltsTactic___redArg(v_attemptAllTk_316_, v_barTks_319_, v_tacticSeqs_318_, v_a_300_, v_a_301_);
lean_dec_ref(v_tacticSeqs_318_);
lean_dec_ref(v_barTks_319_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttemptAll___boxed(lean_object* v_x_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Fmt_fmtAttemptAll(v_x_321_, v_a_322_, v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1(){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = l_Lean_Fmt_fmtAttribute;
v___x_332_ = ((lean_object*)(l_Lean_Fmt_fmtAttemptAll___closed__1));
v___x_333_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___closed__1));
v___x_334_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAttemptAll___boxed), 3, 0);
v___x_335_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_331_, v___x_332_, v___x_333_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1___boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttemptAllPar(lean_object* v_x_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l_Lean_Fmt_fmtAttemptAllPar___closed__1));
lean_inc(v_x_344_);
v___x_348_ = l_Lean_Syntax_isOfKind(v_x_344_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_x_344_);
v___x_349_ = l_Lean_Fmt_Error_partialFormatter;
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_a_346_);
return v___x_350_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; size_t v_sz_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = l_Lean_Syntax_getArg(v_x_344_, v___x_351_);
v___x_353_ = l_Lean_Syntax_getArgs(v___x_352_);
lean_dec(v___x_352_);
v_sz_354_ = lean_array_size(v___x_353_);
v___x_355_ = ((size_t)0ULL);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0(v_sz_354_, v___x_355_, v___x_353_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v_x_344_);
v___x_357_ = l_Lean_Fmt_Error_partialFormatter;
v___x_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_a_346_);
return v___x_358_;
}
else
{
lean_object* v_val_359_; lean_object* v___x_360_; lean_object* v_attemptAllParTk_361_; size_t v_sz_362_; lean_object* v_tacticSeqs_363_; lean_object* v_barTks_364_; lean_object* v___x_365_; 
v_val_359_ = lean_ctor_get(v___x_356_, 0);
lean_inc_n(v_val_359_, 2);
lean_dec_ref_known(v___x_356_, 1);
v___x_360_ = lean_unsigned_to_nat(0u);
v_attemptAllParTk_361_ = l_Lean_Syntax_getArg(v_x_344_, v___x_360_);
lean_dec(v_x_344_);
v_sz_362_ = lean_array_size(v_val_359_);
v_tacticSeqs_363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__1(v_sz_362_, v___x_355_, v_val_359_);
v_barTks_364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__2(v_sz_362_, v___x_355_, v_val_359_);
v___x_365_ = l_Lean_Fmt_fmtAltsTactic___redArg(v_attemptAllParTk_361_, v_barTks_364_, v_tacticSeqs_363_, v_a_345_, v_a_346_);
lean_dec_ref(v_tacticSeqs_363_);
lean_dec_ref(v_barTks_364_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttemptAllPar___boxed(lean_object* v_x_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Fmt_fmtAttemptAllPar(v_x_366_, v_a_367_, v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1(){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_376_ = l_Lean_Fmt_fmtAttribute;
v___x_377_ = ((lean_object*)(l_Lean_Fmt_fmtAttemptAllPar___closed__1));
v___x_378_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___closed__1));
v___x_379_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAttemptAllPar___boxed), 3, 0);
v___x_380_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_376_, v___x_377_, v___x_378_, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1___boxed(lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1();
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFirstPar(lean_object* v_x_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_Fmt_fmtFirstPar___closed__1));
lean_inc(v_x_389_);
v___x_393_ = l_Lean_Syntax_isOfKind(v_x_389_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v_x_389_);
v___x_394_ = l_Lean_Fmt_Error_partialFormatter;
v___x_395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_a_391_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; size_t v_sz_399_; size_t v___x_400_; lean_object* v___x_401_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = l_Lean_Syntax_getArg(v_x_389_, v___x_396_);
v___x_398_ = l_Lean_Syntax_getArgs(v___x_397_);
lean_dec(v___x_397_);
v_sz_399_ = lean_array_size(v___x_398_);
v___x_400_ = ((size_t)0ULL);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__0(v_sz_399_, v___x_400_, v___x_398_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v_x_389_);
v___x_402_ = l_Lean_Fmt_Error_partialFormatter;
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_a_391_);
return v___x_403_;
}
else
{
lean_object* v_val_404_; lean_object* v___x_405_; lean_object* v_firstParTk_406_; size_t v_sz_407_; lean_object* v_tacticSeqs_408_; lean_object* v_barTks_409_; lean_object* v___x_410_; 
v_val_404_ = lean_ctor_get(v___x_401_, 0);
lean_inc_n(v_val_404_, 2);
lean_dec_ref_known(v___x_401_, 1);
v___x_405_ = lean_unsigned_to_nat(0u);
v_firstParTk_406_ = l_Lean_Syntax_getArg(v_x_389_, v___x_405_);
lean_dec(v_x_389_);
v_sz_407_ = lean_array_size(v_val_404_);
v_tacticSeqs_408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__1(v_sz_407_, v___x_400_, v_val_404_);
v_barTks_409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtAttemptAll_spec__2(v_sz_407_, v___x_400_, v_val_404_);
v___x_410_ = l_Lean_Fmt_fmtAltsTactic___redArg(v_firstParTk_406_, v_barTks_409_, v_tacticSeqs_408_, v_a_390_, v_a_391_);
lean_dec_ref(v_tacticSeqs_408_);
lean_dec_ref(v_barTks_409_);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFirstPar___boxed(lean_object* v_x_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Fmt_fmtFirstPar(v_x_411_, v_a_412_, v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1(){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_421_ = l_Lean_Fmt_fmtAttribute;
v___x_422_ = ((lean_object*)(l_Lean_Fmt_fmtFirstPar___closed__1));
v___x_423_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___closed__1));
v___x_424_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtFirstPar___boxed), 3, 0);
v___x_425_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_421_, v___x_422_, v___x_423_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1___boxed(lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1();
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryResult(lean_object* v_x_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_Fmt_fmtTryResult___closed__1));
lean_inc(v_x_434_);
v___x_438_ = l_Lean_Syntax_isOfKind(v_x_434_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v_x_434_);
v___x_439_ = l_Lean_Fmt_Error_partialFormatter;
v___x_440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_a_436_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; lean_object* v_trySuggestionsTk_442_; lean_object* v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v_trySuggestionsTk_442_ = l_Lean_Syntax_getArg(v_x_434_, v___x_441_);
v___x_443_ = l_Lean_Fmt_fmt(v_trySuggestionsTk_442_, v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v_a_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_tactics_448_; lean_object* v___x_449_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
v_a_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_443_, 2);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = l_Lean_Syntax_getArg(v_x_434_, v___x_446_);
lean_dec(v_x_434_);
v_tactics_448_ = l_Lean_Syntax_getArgs(v___x_447_);
lean_dec(v___x_447_);
v___x_449_ = l_Lean_Fmt_fmtArray___redArg(v_tactics_448_, v_a_435_, v_a_445_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_464_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_a_451_ = lean_ctor_get(v___x_449_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_464_ == 0)
{
v___x_453_ = v___x_449_;
v_isShared_454_ = v_isSharedCheck_464_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_464_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_455_ = lean_mk_empty_array_with_capacity(v___x_446_);
v___x_456_ = lean_array_push(v___x_455_, v_a_444_);
v___x_457_ = l_Array_append___redArg(v___x_456_, v_a_450_);
lean_dec(v_a_450_);
v___x_458_ = 0;
v___x_459_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_459_, 0, v___x_438_);
lean_ctor_set_uint8(v___x_459_, 1, v___x_458_);
lean_ctor_set_uint8(v___x_459_, 2, v___x_458_);
lean_ctor_set_uint8(v___x_459_, 3, v___x_458_);
v___x_460_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_457_, v___x_459_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_460_);
v___x_462_ = v___x_453_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_a_451_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_a_444_);
v_a_465_ = lean_ctor_get(v___x_449_, 0);
v_a_466_ = lean_ctor_get(v___x_449_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_449_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_inc(v_a_465_);
lean_dec(v___x_449_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
lean_dec(v_x_434_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryResult___boxed(lean_object* v_x_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Fmt_fmtTryResult(v_x_474_, v_a_475_, v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1(){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = l_Lean_Fmt_fmtAttribute;
v___x_485_ = ((lean_object*)(l_Lean_Fmt_fmtTryResult___closed__1));
v___x_486_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___closed__1));
v___x_487_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTryResult___boxed), 3, 0);
v___x_488_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_484_, v___x_485_, v___x_486_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1___boxed(lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1();
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterTryTactic(lean_object* v_x_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterTryTactic___closed__2));
lean_inc(v_x_509_);
v___x_513_ = l_Lean_Syntax_isOfKind(v_x_509_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_x_509_);
v___x_514_ = l_Lean_Fmt_Error_partialFormatter;
v___x_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_a_511_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v_lbTk_x3f_549_; lean_object* v_priorityTk_x3f_550_; lean_object* v_colonEqTk_x3f_551_; lean_object* v_priority_x3f_552_; lean_object* v_rbTk_x3f_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v_docComment_x3f_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_606_ = l_Lean_Syntax_getArg(v_x_509_, v___x_516_);
v___x_607_ = l_Lean_Syntax_isNone(v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_606_);
v___x_609_ = l_Lean_Syntax_matchesNull(v___x_606_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v___x_606_);
lean_dec(v_x_509_);
v___x_610_ = l_Lean_Fmt_Error_partialFormatter;
v___x_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v_a_511_);
return v___x_611_;
}
else
{
lean_object* v_docComment_x3f_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_docComment_x3f_612_ = l_Lean_Syntax_getArg(v___x_606_, v___x_516_);
lean_dec(v___x_606_);
v___x_613_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterTryTactic___closed__7));
lean_inc(v_docComment_x3f_612_);
v___x_614_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_docComment_x3f_612_);
lean_dec(v_x_509_);
v___x_615_ = l_Lean_Fmt_Error_partialFormatter;
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_a_511_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_docComment_x3f_612_);
v_docComment_x3f_577_ = v___x_617_;
v___y_578_ = v_a_510_;
v___y_579_ = v_a_511_;
goto v___jp_576_;
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec(v___x_606_);
v___x_618_ = lean_box(0);
v_docComment_x3f_577_ = v___x_618_;
v___y_578_ = v_a_510_;
v___y_579_ = v_a_511_;
goto v___jp_576_;
}
v___jp_517_:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_523_, v___y_524_, v___y_526_, v___y_527_, v___y_521_, v___y_522_, v___y_520_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v_a_530_; lean_object* v___x_531_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
v_a_530_ = lean_ctor_get(v___x_528_, 1);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_528_, 2);
v___x_531_ = l_Lean_Fmt_fmt(v___y_519_, v___y_522_, v_a_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
v_a_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_531_, 2);
v___x_534_ = lean_unsigned_to_nat(2u);
v___x_535_ = lean_mk_empty_array_with_capacity(v___x_534_);
v___x_536_ = lean_array_push(v___x_535_, v___y_525_);
v___x_537_ = lean_array_push(v___x_536_, v_a_529_);
v___x_538_ = 0;
v___x_539_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_539_, 0, v___x_513_);
lean_ctor_set_uint8(v___x_539_, 1, v___x_538_);
lean_ctor_set_uint8(v___x_539_, 2, v___x_538_);
lean_ctor_set_uint8(v___x_539_, 3, v___x_538_);
v___x_540_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_537_, v___x_539_);
v___x_541_ = 1;
v___x_542_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v___x_540_, v_a_532_, v___x_541_);
v___x_543_ = lean_box(0);
v___x_544_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterTryTactic___closed__3));
v___x_545_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_518_, v___x_543_, v___x_544_, v___x_542_, v___y_522_, v_a_533_);
return v___x_545_;
}
else
{
lean_dec(v_a_529_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_518_);
return v___x_531_;
}
}
else
{
lean_dec_ref(v___y_525_);
lean_dec(v___y_519_);
lean_dec(v___y_518_);
return v___x_528_;
}
}
v___jp_546_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_556_ = lean_unsigned_to_nat(3u);
v___x_557_ = l_Lean_Syntax_getArg(v_x_509_, v___x_556_);
lean_dec(v_x_509_);
v___x_558_ = ((lean_object*)(l_Lean_Fmt_fmtTryTraceWith___closed__3));
lean_inc(v___x_557_);
v___x_559_ = l_Lean_Syntax_isOfKind(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v___x_557_);
lean_dec(v_rbTk_x3f_553_);
lean_dec(v_priority_x3f_552_);
lean_dec(v_colonEqTk_x3f_551_);
lean_dec(v_priorityTk_x3f_550_);
lean_dec(v_lbTk_x3f_549_);
lean_dec(v___y_548_);
lean_dec(v___y_547_);
v___x_560_ = l_Lean_Fmt_Error_partialFormatter;
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___y_555_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Fmt_fmt(v___y_548_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_562_) == 0)
{
if (lean_obj_tag(v_priority_x3f_552_) == 0)
{
lean_object* v_a_563_; lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
v_a_564_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_562_, 2);
v___x_565_ = lean_box(0);
v___y_518_ = v___y_547_;
v___y_519_ = v___x_557_;
v___y_520_ = v_a_564_;
v___y_521_ = v_rbTk_x3f_553_;
v___y_522_ = v___y_554_;
v___y_523_ = v_lbTk_x3f_549_;
v___y_524_ = v_priorityTk_x3f_550_;
v___y_525_ = v_a_563_;
v___y_526_ = v_colonEqTk_x3f_551_;
v___y_527_ = v___x_565_;
goto v___jp_517_;
}
else
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v_val_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_566_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_566_);
v_a_567_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_562_, 2);
v_val_568_ = lean_ctor_get(v_priority_x3f_552_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_priority_x3f_552_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v_priority_x3f_552_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_val_568_);
lean_dec(v_priority_x3f_552_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_val_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v___y_518_ = v___y_547_;
v___y_519_ = v___x_557_;
v___y_520_ = v_a_567_;
v___y_521_ = v_rbTk_x3f_553_;
v___y_522_ = v___y_554_;
v___y_523_ = v_lbTk_x3f_549_;
v___y_524_ = v_priorityTk_x3f_550_;
v___y_525_ = v_a_566_;
v___y_526_ = v_colonEqTk_x3f_551_;
v___y_527_ = v___x_573_;
goto v___jp_517_;
}
}
}
}
else
{
lean_dec(v___x_557_);
lean_dec(v_rbTk_x3f_553_);
lean_dec(v_priority_x3f_552_);
lean_dec(v_colonEqTk_x3f_551_);
lean_dec(v_priorityTk_x3f_550_);
lean_dec(v_lbTk_x3f_549_);
lean_dec(v___y_547_);
return v___x_562_;
}
}
}
v___jp_576_:
{
lean_object* v___x_580_; lean_object* v_registerTk_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v_registerTk_581_ = l_Lean_Syntax_getArg(v_x_509_, v___x_580_);
v___x_582_ = lean_unsigned_to_nat(2u);
v___x_583_ = l_Lean_Syntax_getArg(v_x_509_, v___x_582_);
v___x_584_ = l_Lean_Syntax_isNone(v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_583_);
v___x_586_ = l_Lean_Syntax_matchesNull(v___x_583_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v___x_583_);
lean_dec(v_registerTk_581_);
lean_dec(v_docComment_x3f_577_);
lean_dec(v_x_509_);
v___x_587_ = l_Lean_Fmt_Error_partialFormatter;
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___y_579_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v_priority_x3f_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_589_ = lean_unsigned_to_nat(3u);
v_priority_x3f_590_ = l_Lean_Syntax_getArg(v___x_583_, v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterTryTactic___closed__5));
lean_inc(v_priority_x3f_590_);
v___x_592_ = l_Lean_Syntax_isOfKind(v_priority_x3f_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_priority_x3f_590_);
lean_dec(v___x_583_);
lean_dec(v_registerTk_581_);
lean_dec(v_docComment_x3f_577_);
lean_dec(v_x_509_);
v___x_593_ = l_Lean_Fmt_Error_partialFormatter;
v___x_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___y_579_);
return v___x_594_;
}
else
{
lean_object* v_lbTk_x3f_595_; lean_object* v_priorityTk_x3f_596_; lean_object* v_colonEqTk_x3f_597_; lean_object* v___x_598_; lean_object* v_rbTk_x3f_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_lbTk_x3f_595_ = l_Lean_Syntax_getArg(v___x_583_, v___x_516_);
v_priorityTk_x3f_596_ = l_Lean_Syntax_getArg(v___x_583_, v___x_580_);
v_colonEqTk_x3f_597_ = l_Lean_Syntax_getArg(v___x_583_, v___x_582_);
v___x_598_ = lean_unsigned_to_nat(4u);
v_rbTk_x3f_599_ = l_Lean_Syntax_getArg(v___x_583_, v___x_598_);
lean_dec(v___x_583_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_lbTk_x3f_595_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_priorityTk_x3f_596_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_colonEqTk_x3f_597_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v_priority_x3f_590_);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v_rbTk_x3f_599_);
v___y_547_ = v_docComment_x3f_577_;
v___y_548_ = v_registerTk_581_;
v_lbTk_x3f_549_ = v___x_600_;
v_priorityTk_x3f_550_ = v___x_601_;
v_colonEqTk_x3f_551_ = v___x_602_;
v_priority_x3f_552_ = v___x_603_;
v_rbTk_x3f_553_ = v___x_604_;
v___y_554_ = v___y_578_;
v___y_555_ = v___y_579_;
goto v___jp_546_;
}
}
}
else
{
lean_object* v___x_605_; 
lean_dec(v___x_583_);
v___x_605_ = lean_box(0);
v___y_547_ = v_docComment_x3f_577_;
v___y_548_ = v_registerTk_581_;
v_lbTk_x3f_549_ = v___x_605_;
v_priorityTk_x3f_550_ = v___x_605_;
v_colonEqTk_x3f_551_ = v___x_605_;
v_priority_x3f_552_ = v___x_605_;
v_rbTk_x3f_553_ = v___x_605_;
v___y_554_ = v___y_578_;
v___y_555_ = v___y_579_;
goto v___jp_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterTryTactic___boxed(lean_object* v_x_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Fmt_fmtRegisterTryTactic(v_x_619_, v_a_620_, v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1(){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_629_ = l_Lean_Fmt_fmtAttribute;
v___x_630_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterTryTactic___closed__2));
v___x_631_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___closed__1));
v___x_632_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterTryTactic___boxed), 3, 0);
v___x_633_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_629_, v___x_630_, v___x_631_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1___boxed(lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1();
return v_res_635_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Try(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTrace___regBuiltin_Lean_Fmt_fmtTryTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryTraceWith___regBuiltin_Lean_Fmt_fmtTryTraceWith__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAll___regBuiltin_Lean_Fmt_fmtAttemptAll__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtAttemptAllPar___regBuiltin_Lean_Fmt_fmtAttemptAllPar__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtFirstPar___regBuiltin_Lean_Fmt_fmtFirstPar__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtTryResult___regBuiltin_Lean_Fmt_fmtTryResult__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Try_0__Lean_Fmt_fmtRegisterTryTactic___regBuiltin_Lean_Fmt_fmtRegisterTryTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Try(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Try(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Try(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Try(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Try(builtin);
}
#ifdef __cplusplus
}
#endif
