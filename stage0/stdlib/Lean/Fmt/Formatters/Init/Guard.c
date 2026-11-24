// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Guard
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Guard import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardColon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardColon___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colon"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 254, 84, 58, 178, 14, 199, 231)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGuardColon"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(217, 151, 25, 252, 6, 51, 161, 59)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__6 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardColonEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardColonEq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "colonEq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 195, 203, 230, 89, 211, 239, 47)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGuardColonEq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(183, 237, 0, 65, 91, 249, 11, 203)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardEqual(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardEqual___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "equal"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 80, 62, 47, 176, 56, 79, 244)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGuardEqual"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(198, 59, 199, 143, 35, 96, 60, 120)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGuardExprLike___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardExprLike___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGuardExprLike___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardExprLike___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtGuardExpr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGuardExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "guardExpr"};
static const lean_object* l_Lean_Fmt_fmtGuardExpr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExpr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 0, 57, 230, 6, 90, 102, 33)}};
static const lean_object* l_Lean_Fmt_fmtGuardExpr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGuardExpr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 94, 165, 38, 82, 211, 51, 5)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardExprConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "guardExprConv"};
static const lean_object* l_Lean_Fmt_fmtGuardExprConv___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardExprConv___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprConv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprConv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExprConv___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprConv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExprConv___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprConv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExprConv___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardExprConv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 204, 249, 180, 228, 44, 37, 243)}};
static const lean_object* l_Lean_Fmt_fmtGuardExprConv___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardExprConv___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprConv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprConv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGuardExprConv"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 126, 12, 125, 170, 88, 153, 89)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardExprCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtGuardExprCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGuardExprCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "guardExprCmd"};
static const lean_object* l_Lean_Fmt_fmtGuardExprCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprCmd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprCmd___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprCmd___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardExprCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 243, 228, 205, 228, 23, 93, 39)}};
static const lean_object* l_Lean_Fmt_fmtGuardExprCmd___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGuardExprCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 165, 172, 99, 49, 70, 20, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTargetLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTargetLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "guardTarget"};
static const lean_object* l_Lean_Fmt_fmtGuardTarget___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardTarget___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardTarget___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardTarget___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardTarget___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardTarget___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardTarget___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardTarget___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 4, 80, 225, 8, 32, 178, 134)}};
static const lean_object* l_Lean_Fmt_fmtGuardTarget___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardTarget___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTarget___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtGuardTarget"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 193, 186, 185, 132, 33, 72, 90)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardTargetConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "guardTargetConv"};
static const lean_object* l_Lean_Fmt_fmtGuardTargetConv___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardTargetConv___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardTargetConv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardTargetConv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardTargetConv___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardTargetConv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardTargetConv___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardTargetConv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardTargetConv___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardTargetConv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 167, 126, 167, 155, 13, 186, 15)}};
static const lean_object* l_Lean_Fmt_fmtGuardTargetConv___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardTargetConv___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTargetConv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTargetConv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtGuardTargetConv"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 87, 135, 206, 232, 120, 77, 243)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtGuardHypLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGuardHypLike___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardHypLike___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHypLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHypLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "guardHyp"};
static const lean_object* l_Lean_Fmt_fmtGuardHyp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardHyp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardHyp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardHyp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardHyp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardHyp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardHyp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardHyp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardHyp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 79, 231, 38, 72, 47, 167, 177)}};
static const lean_object* l_Lean_Fmt_fmtGuardHyp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardHyp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHyp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHyp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGuardHyp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 167, 84, 129, 91, 92, 221, 63)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardHypConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "guardHypConv"};
static const lean_object* l_Lean_Fmt_fmtGuardHypConv___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardHypConv___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardHypConv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardHypConv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardHypConv___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardHypConv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardHypConv___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardHypConv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardHypConv___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardHypConv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 4, 67, 240, 71, 133, 21, 138)}};
static const lean_object* l_Lean_Fmt_fmtGuardHypConv___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardHypConv___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHypConv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHypConv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGuardHypConv"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 106, 1, 115, 249, 132, 51, 42)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "guardCmd"};
static const lean_object* l_Lean_Fmt_fmtGuardCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardCmd___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardCmd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardExprCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardCmd___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 150, 251, 111, 125, 167, 179, 116)}};
static const lean_object* l_Lean_Fmt_fmtGuardCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtGuardCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 203, 210, 129, 27, 14, 244, 75)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardColon(lean_object* v_stx_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_1_, v___x_4_, v_a_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v_a_7_; lean_object* v___x_8_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_a_6_);
v_a_7_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_a_7_);
lean_dec_ref_known(v___x_5_, 2);
v___x_8_ = l_Lean_Fmt_fmt(v_a_6_, v_a_2_, v_a_7_);
return v___x_8_;
}
else
{
lean_object* v_a_9_; lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_17_; 
v_a_9_ = lean_ctor_get(v___x_5_, 0);
v_a_10_ = lean_ctor_get(v___x_5_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_17_ == 0)
{
v___x_12_ = v___x_5_;
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_inc(v_a_9_);
lean_dec(v___x_5_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_a_9_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_a_10_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardColon___boxed(lean_object* v_stx_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Fmt_fmtGuardColon(v_stx_18_, v_a_19_, v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_stx_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1(){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_36_ = l_Lean_Fmt_fmtAttribute;
v___x_37_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3));
v___x_38_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__6));
v___x_39_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardColon___boxed), 3, 0);
v___x_40_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_36_, v___x_37_, v___x_38_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___boxed(lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1();
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardColonEq(lean_object* v_stx_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_43_, v___x_46_, v_a_45_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_50_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
v_a_49_ = lean_ctor_get(v___x_47_, 1);
lean_inc(v_a_49_);
lean_dec_ref_known(v___x_47_, 2);
v___x_50_ = l_Lean_Fmt_fmt(v_a_48_, v_a_44_, v_a_49_);
return v___x_50_;
}
else
{
lean_object* v_a_51_; lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
v_a_51_ = lean_ctor_get(v___x_47_, 0);
v_a_52_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_47_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_inc(v_a_51_);
lean_dec(v___x_47_);
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
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_51_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardColonEq___boxed(lean_object* v_stx_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Fmt_fmtGuardColonEq(v_stx_60_, v_a_61_, v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_stx_60_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1(){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_75_ = l_Lean_Fmt_fmtAttribute;
v___x_76_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1));
v___x_77_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__3));
v___x_78_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardColonEq___boxed), 3, 0);
v___x_79_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_75_, v___x_76_, v___x_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___boxed(lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1();
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardEqual(lean_object* v_stx_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_82_, v___x_85_, v_a_84_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v_a_88_; lean_object* v___x_89_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_87_);
v_a_88_ = lean_ctor_get(v___x_86_, 1);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_86_, 2);
v___x_89_ = l_Lean_Fmt_fmt(v_a_87_, v_a_83_, v_a_88_);
return v___x_89_;
}
else
{
lean_object* v_a_90_; lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_a_90_ = lean_ctor_get(v___x_86_, 0);
v_a_91_ = lean_ctor_get(v___x_86_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_86_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_inc(v_a_90_);
lean_dec(v___x_86_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_90_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardEqual___boxed(lean_object* v_stx_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Fmt_fmtGuardEqual(v_stx_99_, v_a_100_, v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_stx_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1(){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_114_ = l_Lean_Fmt_fmtAttribute;
v___x_115_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1));
v___x_116_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__3));
v___x_117_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardEqual___boxed), 3, 0);
v___x_118_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_114_, v___x_115_, v___x_116_, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___boxed(lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1();
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprLike(lean_object* v_guardExprTk_127_, lean_object* v_lhs_128_, lean_object* v_equal_129_, lean_object* v_rhs_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Fmt_fmt(v_guardExprTk_127_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v_a_135_; lean_object* v___x_136_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
v_a_135_ = lean_ctor_get(v___x_133_, 1);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_133_, 2);
v___x_136_ = l_Lean_Fmt_fmt(v_lhs_128_, v_a_131_, v_a_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v_a_138_; lean_object* v___x_139_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
v_a_138_ = lean_ctor_get(v___x_136_, 1);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_136_, 2);
v___x_139_ = l_Lean_Fmt_fmt(v_equal_129_, v_a_131_, v_a_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v_a_141_; lean_object* v___x_142_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
v_a_141_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_139_, 2);
v___x_142_ = l_Lean_Fmt_fmt(v_rhs_130_, v_a_131_, v_a_141_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_164_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_a_144_ = lean_ctor_get(v___x_142_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_164_ == 0)
{
v___x_146_ = v___x_142_;
v_isShared_147_ = v_isSharedCheck_164_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_164_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_148_ = lean_unsigned_to_nat(3u);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_148_);
v___x_150_ = lean_array_push(v___x_149_, v_a_137_);
v___x_151_ = lean_array_push(v___x_150_, v_a_140_);
v___x_152_ = lean_array_push(v___x_151_, v_a_143_);
v___x_153_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprLike___closed__0));
v___x_154_ = l_Lean_Fmt_Layouts_infixOperator(v___x_152_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(2u);
v___x_156_ = lean_mk_empty_array_with_capacity(v___x_155_);
v___x_157_ = lean_array_push(v___x_156_, v_a_134_);
v___x_158_ = lean_array_push(v___x_157_, v___x_154_);
v___x_159_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprLike___closed__1));
v___x_160_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_158_, v___x_159_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_160_);
v___x_162_ = v___x_146_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_a_144_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_dec(v_a_140_);
lean_dec(v_a_137_);
lean_dec(v_a_134_);
return v___x_142_;
}
}
else
{
lean_dec(v_a_137_);
lean_dec(v_a_134_);
lean_dec(v_rhs_130_);
return v___x_139_;
}
}
else
{
lean_dec(v_a_134_);
lean_dec(v_rhs_130_);
lean_dec(v_equal_129_);
return v___x_136_;
}
}
else
{
lean_dec(v_rhs_130_);
lean_dec(v_equal_129_);
lean_dec(v_lhs_128_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprLike___boxed(lean_object* v_guardExprTk_165_, lean_object* v_lhs_166_, lean_object* v_equal_167_, lean_object* v_rhs_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Fmt_fmtGuardExprLike(v_guardExprTk_165_, v_lhs_166_, v_equal_167_, v_rhs_168_, v_a_169_, v_a_170_);
lean_dec_ref(v_a_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExpr(lean_object* v_x_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExpr___closed__2));
lean_inc(v_x_179_);
v___x_183_ = l_Lean_Syntax_isOfKind(v_x_179_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v_x_179_);
v___x_184_ = l_Lean_Fmt_Error_partialFormatter;
v___x_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_181_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_186_ = lean_unsigned_to_nat(2u);
v___x_187_ = l_Lean_Syntax_getArg(v_x_179_, v___x_186_);
v___x_188_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1));
lean_inc(v___x_187_);
v___x_189_ = l_Lean_Syntax_isOfKind(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v___x_187_);
lean_dec(v_x_179_);
v___x_190_ = l_Lean_Fmt_Error_partialFormatter;
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_a_181_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; lean_object* v_guardExprTk_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v_guardExprTk_193_ = l_Lean_Syntax_getArg(v_x_179_, v___x_192_);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = l_Lean_Syntax_getArg(v_x_179_, v___x_194_);
v___x_196_ = lean_unsigned_to_nat(3u);
v___x_197_ = l_Lean_Syntax_getArg(v_x_179_, v___x_196_);
lean_dec(v_x_179_);
v___x_198_ = l_Lean_Fmt_fmtGuardExprLike(v_guardExprTk_193_, v___x_195_, v___x_187_, v___x_197_, v_a_180_, v_a_181_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExpr___boxed(lean_object* v_x_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Fmt_fmtGuardExpr(v_x_199_, v_a_200_, v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1(){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_209_ = l_Lean_Fmt_fmtAttribute;
v___x_210_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExpr___closed__2));
v___x_211_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___closed__1));
v___x_212_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardExpr___boxed), 3, 0);
v___x_213_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_209_, v___x_210_, v___x_211_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1___boxed(lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1();
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprConv(lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprConv___closed__1));
lean_inc(v_x_222_);
v___x_226_ = l_Lean_Syntax_isOfKind(v_x_222_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v_x_222_);
v___x_227_ = l_Lean_Fmt_Error_partialFormatter;
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_a_224_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_229_ = lean_unsigned_to_nat(2u);
v___x_230_ = l_Lean_Syntax_getArg(v_x_222_, v___x_229_);
v___x_231_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1));
lean_inc(v___x_230_);
v___x_232_ = l_Lean_Syntax_isOfKind(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v___x_230_);
lean_dec(v_x_222_);
v___x_233_ = l_Lean_Fmt_Error_partialFormatter;
v___x_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v_a_224_);
return v___x_234_;
}
else
{
lean_object* v___x_235_; lean_object* v_guardExprTk_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v_guardExprTk_236_ = l_Lean_Syntax_getArg(v_x_222_, v___x_235_);
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = l_Lean_Syntax_getArg(v_x_222_, v___x_237_);
v___x_239_ = lean_unsigned_to_nat(3u);
v___x_240_ = l_Lean_Syntax_getArg(v_x_222_, v___x_239_);
lean_dec(v_x_222_);
v___x_241_ = l_Lean_Fmt_fmtGuardExprLike(v_guardExprTk_236_, v___x_238_, v___x_230_, v___x_240_, v_a_223_, v_a_224_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprConv___boxed(lean_object* v_x_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Fmt_fmtGuardExprConv(v_x_242_, v_a_243_, v_a_244_);
lean_dec_ref(v_a_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1(){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_252_ = l_Lean_Fmt_fmtAttribute;
v___x_253_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprConv___closed__1));
v___x_254_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___closed__1));
v___x_255_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardExprConv___boxed), 3, 0);
v___x_256_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_252_, v___x_253_, v___x_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1___boxed(lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1();
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprCmd(lean_object* v_x_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprCmd___closed__2));
lean_inc(v_x_266_);
v___x_270_ = l_Lean_Syntax_isOfKind(v_x_266_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_x_266_);
v___x_271_ = l_Lean_Fmt_Error_partialFormatter;
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_a_268_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_273_ = lean_unsigned_to_nat(2u);
v___x_274_ = l_Lean_Syntax_getArg(v_x_266_, v___x_273_);
v___x_275_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1));
lean_inc(v___x_274_);
v___x_276_ = l_Lean_Syntax_isOfKind(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v___x_274_);
lean_dec(v_x_266_);
v___x_277_ = l_Lean_Fmt_Error_partialFormatter;
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_268_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v_guardExprTk_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v_guardExprTk_280_ = l_Lean_Syntax_getArg(v_x_266_, v___x_279_);
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = l_Lean_Syntax_getArg(v_x_266_, v___x_281_);
v___x_283_ = lean_unsigned_to_nat(3u);
v___x_284_ = l_Lean_Syntax_getArg(v_x_266_, v___x_283_);
lean_dec(v_x_266_);
v___x_285_ = l_Lean_Fmt_fmtGuardExprLike(v_guardExprTk_280_, v___x_282_, v___x_274_, v___x_284_, v_a_267_, v_a_268_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardExprCmd___boxed(lean_object* v_x_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Fmt_fmtGuardExprCmd(v_x_286_, v_a_287_, v_a_288_);
lean_dec_ref(v_a_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1(){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_296_ = l_Lean_Fmt_fmtAttribute;
v___x_297_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprCmd___closed__2));
v___x_298_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___closed__1));
v___x_299_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardExprCmd___boxed), 3, 0);
v___x_300_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_296_, v___x_297_, v___x_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1___boxed(lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1();
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTargetLike(lean_object* v_guardTargetTk_303_, lean_object* v_equal_304_, lean_object* v_rhs_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Fmt_fmt(v_guardTargetTk_303_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v_a_310_; lean_object* v___x_311_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
v_a_310_ = lean_ctor_get(v___x_308_, 1);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_308_, 2);
v___x_311_ = l_Lean_Fmt_fmt(v_equal_304_, v_a_306_, v_a_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v_a_313_; lean_object* v___x_314_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
v_a_313_ = lean_ctor_get(v___x_311_, 1);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_311_, 2);
v___x_314_ = l_Lean_Fmt_fmt(v_rhs_305_, v_a_306_, v_a_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_331_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_a_316_ = lean_ctor_get(v___x_314_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_331_ == 0)
{
v___x_318_ = v___x_314_;
v_isShared_319_ = v_isSharedCheck_331_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_331_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_320_ = 2;
v___x_321_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_312_, v_a_315_, v___x_320_);
v___x_322_ = lean_unsigned_to_nat(2u);
v___x_323_ = lean_mk_empty_array_with_capacity(v___x_322_);
v___x_324_ = lean_array_push(v___x_323_, v_a_309_);
v___x_325_ = lean_array_push(v___x_324_, v___x_321_);
v___x_326_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprLike___closed__1));
v___x_327_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_325_, v___x_326_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_327_);
v___x_329_ = v___x_318_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_a_316_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_dec(v_a_312_);
lean_dec(v_a_309_);
return v___x_314_;
}
}
else
{
lean_dec(v_a_309_);
lean_dec(v_rhs_305_);
return v___x_311_;
}
}
else
{
lean_dec(v_rhs_305_);
lean_dec(v_equal_304_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTargetLike___boxed(lean_object* v_guardTargetTk_332_, lean_object* v_equal_333_, lean_object* v_rhs_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Fmt_fmtGuardTargetLike(v_guardTargetTk_332_, v_equal_333_, v_rhs_334_, v_a_335_, v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTarget(lean_object* v_x_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l_Lean_Fmt_fmtGuardTarget___closed__1));
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
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = l_Lean_Syntax_getArg(v_x_344_, v___x_351_);
v___x_353_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1));
lean_inc(v___x_352_);
v___x_354_ = l_Lean_Syntax_isOfKind(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v___x_352_);
lean_dec(v_x_344_);
v___x_355_ = l_Lean_Fmt_Error_partialFormatter;
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_a_346_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v_guardTargetTk_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_357_ = lean_unsigned_to_nat(0u);
v_guardTargetTk_358_ = l_Lean_Syntax_getArg(v_x_344_, v___x_357_);
v___x_359_ = lean_unsigned_to_nat(2u);
v___x_360_ = l_Lean_Syntax_getArg(v_x_344_, v___x_359_);
lean_dec(v_x_344_);
v___x_361_ = l_Lean_Fmt_fmtGuardTargetLike(v_guardTargetTk_358_, v___x_352_, v___x_360_, v_a_345_, v_a_346_);
return v___x_361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTarget___boxed(lean_object* v_x_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Fmt_fmtGuardTarget(v_x_362_, v_a_363_, v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1(){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = l_Lean_Fmt_fmtAttribute;
v___x_373_ = ((lean_object*)(l_Lean_Fmt_fmtGuardTarget___closed__1));
v___x_374_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___closed__1));
v___x_375_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardTarget___boxed), 3, 0);
v___x_376_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_372_, v___x_373_, v___x_374_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1___boxed(lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1();
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTargetConv(lean_object* v_x_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_Fmt_fmtGuardTargetConv___closed__1));
lean_inc(v_x_385_);
v___x_389_ = l_Lean_Syntax_isOfKind(v_x_385_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_x_385_);
v___x_390_ = l_Lean_Fmt_Error_partialFormatter;
v___x_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_a_387_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = l_Lean_Syntax_getArg(v_x_385_, v___x_392_);
v___x_394_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1___closed__1));
lean_inc(v___x_393_);
v___x_395_ = l_Lean_Syntax_isOfKind(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v___x_393_);
lean_dec(v_x_385_);
v___x_396_ = l_Lean_Fmt_Error_partialFormatter;
v___x_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_a_387_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v_guardTargetTk_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v_guardTargetTk_399_ = l_Lean_Syntax_getArg(v_x_385_, v___x_398_);
v___x_400_ = lean_unsigned_to_nat(2u);
v___x_401_ = l_Lean_Syntax_getArg(v_x_385_, v___x_400_);
lean_dec(v_x_385_);
v___x_402_ = l_Lean_Fmt_fmtGuardTargetLike(v_guardTargetTk_399_, v___x_393_, v___x_401_, v_a_386_, v_a_387_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardTargetConv___boxed(lean_object* v_x_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Fmt_fmtGuardTargetConv(v_x_403_, v_a_404_, v_a_405_);
lean_dec_ref(v_a_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1(){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_413_ = l_Lean_Fmt_fmtAttribute;
v___x_414_ = ((lean_object*)(l_Lean_Fmt_fmtGuardTargetConv___closed__1));
v___x_415_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___closed__1));
v___x_416_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardTargetConv___boxed), 3, 0);
v___x_417_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_413_, v___x_414_, v___x_415_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1___boxed(lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1();
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHypLike(lean_object* v_guardHypTk_423_, lean_object* v_hyp_424_, lean_object* v_colon_x3f_425_, lean_object* v_type_x3f_426_, lean_object* v_colonEq_x3f_427_, lean_object* v_value_x3f_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Fmt_fmt(v_guardHypTk_423_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v_a_433_; lean_object* v___x_434_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
v_a_433_ = lean_ctor_get(v___x_431_, 1);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_431_, 2);
v___x_434_ = l_Lean_Fmt_fmt(v_hyp_424_, v_a_429_, v_a_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
v_a_436_ = lean_ctor_get(v___x_434_, 1);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_434_, 2);
v___x_437_ = l_Lean_Fmt_fmt_x3f(v_colon_x3f_425_, v_a_429_, v_a_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
v_a_439_ = lean_ctor_get(v___x_437_, 1);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_437_, 2);
v___x_440_ = l_Lean_Fmt_fmt_x3f(v_type_x3f_426_, v_a_429_, v_a_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_a_442_; lean_object* v___x_443_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
v_a_442_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_440_, 2);
v___x_443_ = l_Lean_Fmt_fmt_x3f(v_colonEq_x3f_427_, v_a_429_, v_a_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v_a_445_; lean_object* v___x_446_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
v_a_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_443_, 2);
v___x_446_ = l_Lean_Fmt_fmt_x3f(v_value_x3f_428_, v_a_429_, v_a_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_470_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_a_448_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_470_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_470_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_470_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_452_ = ((lean_object*)(l_Lean_Fmt_fmtGuardHypLike___closed__0));
v___x_453_ = l_Lean_Fmt_Layouts_typeAscription(v_a_435_, v_a_438_, v_a_441_, v___x_452_);
v___x_454_ = lean_unsigned_to_nat(3u);
v___x_455_ = lean_mk_empty_array_with_capacity(v___x_454_);
v___x_456_ = lean_array_push(v___x_455_, v___x_453_);
v___x_457_ = lean_array_push(v___x_456_, v_a_444_);
v___x_458_ = lean_array_push(v___x_457_, v_a_447_);
v___x_459_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprLike___closed__0));
v___x_460_ = l_Lean_Fmt_Layouts_infixOperator(v___x_458_, v___x_459_);
v___x_461_ = lean_unsigned_to_nat(2u);
v___x_462_ = lean_mk_empty_array_with_capacity(v___x_461_);
v___x_463_ = lean_array_push(v___x_462_, v_a_432_);
v___x_464_ = lean_array_push(v___x_463_, v___x_460_);
v___x_465_ = ((lean_object*)(l_Lean_Fmt_fmtGuardExprLike___closed__1));
v___x_466_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_464_, v___x_465_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_466_);
v___x_468_ = v___x_450_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_a_448_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_dec(v_a_444_);
lean_dec(v_a_441_);
lean_dec(v_a_438_);
lean_dec(v_a_435_);
lean_dec(v_a_432_);
return v___x_446_;
}
}
else
{
lean_dec(v_a_441_);
lean_dec(v_a_438_);
lean_dec(v_a_435_);
lean_dec(v_a_432_);
lean_dec(v_value_x3f_428_);
return v___x_443_;
}
}
else
{
lean_dec(v_a_438_);
lean_dec(v_a_435_);
lean_dec(v_a_432_);
lean_dec(v_value_x3f_428_);
lean_dec(v_colonEq_x3f_427_);
return v___x_440_;
}
}
else
{
lean_dec(v_a_435_);
lean_dec(v_a_432_);
lean_dec(v_value_x3f_428_);
lean_dec(v_colonEq_x3f_427_);
lean_dec(v_type_x3f_426_);
return v___x_437_;
}
}
else
{
lean_dec(v_a_432_);
lean_dec(v_value_x3f_428_);
lean_dec(v_colonEq_x3f_427_);
lean_dec(v_type_x3f_426_);
lean_dec(v_colon_x3f_425_);
return v___x_434_;
}
}
else
{
lean_dec(v_value_x3f_428_);
lean_dec(v_colonEq_x3f_427_);
lean_dec(v_type_x3f_426_);
lean_dec(v_colon_x3f_425_);
lean_dec(v_hyp_424_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHypLike___boxed(lean_object* v_guardHypTk_471_, lean_object* v_hyp_472_, lean_object* v_colon_x3f_473_, lean_object* v_type_x3f_474_, lean_object* v_colonEq_x3f_475_, lean_object* v_value_x3f_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Fmt_fmtGuardHypLike(v_guardHypTk_471_, v_hyp_472_, v_colon_x3f_473_, v_type_x3f_474_, v_colonEq_x3f_475_, v_value_x3f_476_, v_a_477_, v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHyp(lean_object* v_x_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_Fmt_fmtGuardHyp___closed__1));
lean_inc(v_x_486_);
v___x_490_ = l_Lean_Syntax_isOfKind(v_x_486_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_x_486_);
v___x_491_ = l_Lean_Fmt_Error_partialFormatter;
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_a_488_);
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v_guardHypTk_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v_colonEq_x3f_550_; lean_object* v_value_x3f_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___x_563_; lean_object* v_colon_x3f_565_; lean_object* v_type_x3f_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_493_ = lean_unsigned_to_nat(0u);
v_guardHypTk_494_ = l_Lean_Syntax_getArg(v_x_486_, v___x_493_);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = l_Lean_Syntax_getArg(v_x_486_, v___x_495_);
v___x_563_ = lean_unsigned_to_nat(2u);
v___x_584_ = l_Lean_Syntax_getArg(v_x_486_, v___x_563_);
v___x_585_ = l_Lean_Syntax_isNone(v___x_584_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; 
lean_inc(v___x_584_);
v___x_586_ = l_Lean_Syntax_matchesNull(v___x_584_, v___x_563_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v___x_584_);
lean_dec(v___x_496_);
lean_dec(v_guardHypTk_494_);
lean_dec(v_x_486_);
v___x_587_ = l_Lean_Fmt_Error_partialFormatter;
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_a_488_);
return v___x_588_;
}
else
{
lean_object* v_colon_x3f_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_colon_x3f_589_ = l_Lean_Syntax_getArg(v___x_584_, v___x_493_);
v___x_590_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3));
lean_inc(v_colon_x3f_589_);
v___x_591_ = l_Lean_Syntax_isOfKind(v_colon_x3f_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_colon_x3f_589_);
lean_dec(v___x_584_);
lean_dec(v___x_496_);
lean_dec(v_guardHypTk_494_);
lean_dec(v_x_486_);
v___x_592_ = l_Lean_Fmt_Error_partialFormatter;
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_a_488_);
return v___x_593_;
}
else
{
lean_object* v_type_x3f_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_type_x3f_594_ = l_Lean_Syntax_getArg(v___x_584_, v___x_495_);
lean_dec(v___x_584_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v_colon_x3f_589_);
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v_type_x3f_594_);
v_colon_x3f_565_ = v___x_595_;
v_type_x3f_566_ = v___x_596_;
v___y_567_ = v_a_487_;
v___y_568_ = v_a_488_;
goto v___jp_564_;
}
}
}
else
{
lean_object* v___x_597_; 
lean_dec(v___x_584_);
v___x_597_ = lean_box(0);
v_colon_x3f_565_ = v___x_597_;
v_type_x3f_566_ = v___x_597_;
v___y_567_ = v_a_487_;
v___y_568_ = v_a_488_;
goto v___jp_564_;
}
v___jp_497_:
{
if (lean_obj_tag(v___y_498_) == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_box(0);
v___x_505_ = l_Lean_Fmt_fmtGuardHypLike(v_guardHypTk_494_, v___x_496_, v___y_501_, v___y_502_, v___y_503_, v___x_504_, v___y_500_, v___y_499_);
return v___x_505_;
}
else
{
lean_object* v_val_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
v_val_506_ = lean_ctor_get(v___y_498_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___y_498_);
if (v_isSharedCheck_514_ == 0)
{
v___x_508_ = v___y_498_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_val_506_);
lean_dec(v___y_498_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_val_506_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Fmt_fmtGuardHypLike(v_guardHypTk_494_, v___x_496_, v___y_501_, v___y_502_, v___y_503_, v___x_511_, v___y_500_, v___y_499_);
return v___x_512_;
}
}
}
}
v___jp_515_:
{
if (lean_obj_tag(v___y_517_) == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
v___y_498_ = v___y_516_;
v___y_499_ = v___y_518_;
v___y_500_ = v___y_519_;
v___y_501_ = v___y_520_;
v___y_502_ = v___y_521_;
v___y_503_ = v___x_522_;
goto v___jp_497_;
}
else
{
lean_object* v_val_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_val_523_ = lean_ctor_get(v___y_517_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___y_517_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___y_517_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_val_523_);
lean_dec(v___y_517_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_val_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v___y_498_ = v___y_516_;
v___y_499_ = v___y_518_;
v___y_500_ = v___y_519_;
v___y_501_ = v___y_520_;
v___y_502_ = v___y_521_;
v___y_503_ = v___x_528_;
goto v___jp_497_;
}
}
}
}
v___jp_531_:
{
if (lean_obj_tag(v___y_533_) == 0)
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
v___y_516_ = v___y_532_;
v___y_517_ = v___y_534_;
v___y_518_ = v___y_535_;
v___y_519_ = v___y_536_;
v___y_520_ = v___y_537_;
v___y_521_ = v___x_538_;
goto v___jp_515_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_val_539_ = lean_ctor_get(v___y_533_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___y_533_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___y_533_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v___y_533_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_val_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v___y_516_ = v___y_532_;
v___y_517_ = v___y_534_;
v___y_518_ = v___y_535_;
v___y_519_ = v___y_536_;
v___y_520_ = v___y_537_;
v___y_521_ = v___x_544_;
goto v___jp_515_;
}
}
}
}
v___jp_547_:
{
if (lean_obj_tag(v___y_549_) == 0)
{
lean_object* v___x_554_; 
v___x_554_ = lean_box(0);
v___y_532_ = v_value_x3f_551_;
v___y_533_ = v___y_548_;
v___y_534_ = v_colonEq_x3f_550_;
v___y_535_ = v___y_553_;
v___y_536_ = v___y_552_;
v___y_537_ = v___x_554_;
goto v___jp_531_;
}
else
{
lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_val_555_ = lean_ctor_get(v___y_549_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___y_549_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___y_549_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_dec(v___y_549_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_val_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v___y_532_ = v_value_x3f_551_;
v___y_533_ = v___y_548_;
v___y_534_ = v_colonEq_x3f_550_;
v___y_535_ = v___y_553_;
v___y_536_ = v___y_552_;
v___y_537_ = v___x_560_;
goto v___jp_531_;
}
}
}
}
v___jp_564_:
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_569_ = lean_unsigned_to_nat(3u);
v___x_570_ = l_Lean_Syntax_getArg(v_x_486_, v___x_569_);
lean_dec(v_x_486_);
v___x_571_ = l_Lean_Syntax_isNone(v___x_570_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; 
lean_inc(v___x_570_);
v___x_572_ = l_Lean_Syntax_matchesNull(v___x_570_, v___x_563_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_570_);
lean_dec(v_type_x3f_566_);
lean_dec(v_colon_x3f_565_);
lean_dec(v___x_496_);
lean_dec(v_guardHypTk_494_);
v___x_573_ = l_Lean_Fmt_Error_partialFormatter;
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___y_568_);
return v___x_574_;
}
else
{
lean_object* v_colonEq_x3f_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_colonEq_x3f_575_ = l_Lean_Syntax_getArg(v___x_570_, v___x_493_);
v___x_576_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1));
lean_inc(v_colonEq_x3f_575_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_colonEq_x3f_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_colonEq_x3f_575_);
lean_dec(v___x_570_);
lean_dec(v_type_x3f_566_);
lean_dec(v_colon_x3f_565_);
lean_dec(v___x_496_);
lean_dec(v_guardHypTk_494_);
v___x_578_ = l_Lean_Fmt_Error_partialFormatter;
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___y_568_);
return v___x_579_;
}
else
{
lean_object* v_value_x3f_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_value_x3f_580_ = l_Lean_Syntax_getArg(v___x_570_, v___x_495_);
lean_dec(v___x_570_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v_colonEq_x3f_575_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_value_x3f_580_);
v___y_548_ = v_type_x3f_566_;
v___y_549_ = v_colon_x3f_565_;
v_colonEq_x3f_550_ = v___x_581_;
v_value_x3f_551_ = v___x_582_;
v___y_552_ = v___y_567_;
v___y_553_ = v___y_568_;
goto v___jp_547_;
}
}
}
else
{
lean_object* v___x_583_; 
lean_dec(v___x_570_);
v___x_583_ = lean_box(0);
v___y_548_ = v_type_x3f_566_;
v___y_549_ = v_colon_x3f_565_;
v_colonEq_x3f_550_ = v___x_583_;
v_value_x3f_551_ = v___x_583_;
v___y_552_ = v___y_567_;
v___y_553_ = v___y_568_;
goto v___jp_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHyp___boxed(lean_object* v_x_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Fmt_fmtGuardHyp(v_x_598_, v_a_599_, v_a_600_);
lean_dec_ref(v_a_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1(){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_608_ = l_Lean_Fmt_fmtAttribute;
v___x_609_ = ((lean_object*)(l_Lean_Fmt_fmtGuardHyp___closed__1));
v___x_610_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___closed__1));
v___x_611_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardHyp___boxed), 3, 0);
v___x_612_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_608_, v___x_609_, v___x_610_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1___boxed(lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1();
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHypConv(lean_object* v_x_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Fmt_fmtGuardHypConv___closed__1));
lean_inc(v_x_621_);
v___x_625_ = l_Lean_Syntax_isOfKind(v_x_621_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec(v_x_621_);
v___x_626_ = l_Lean_Fmt_Error_partialFormatter;
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_a_623_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v_guardHypTk_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v_colonEq_x3f_685_; lean_object* v_value_x3f_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___x_698_; lean_object* v_colon_x3f_700_; lean_object* v_type_x3f_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v_guardHypTk_629_ = l_Lean_Syntax_getArg(v_x_621_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = l_Lean_Syntax_getArg(v_x_621_, v___x_630_);
v___x_698_ = lean_unsigned_to_nat(2u);
v___x_719_ = l_Lean_Syntax_getArg(v_x_621_, v___x_698_);
v___x_720_ = l_Lean_Syntax_isNone(v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
lean_inc(v___x_719_);
v___x_721_ = l_Lean_Syntax_matchesNull(v___x_719_, v___x_698_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v___x_719_);
lean_dec(v___x_631_);
lean_dec(v_guardHypTk_629_);
lean_dec(v_x_621_);
v___x_722_ = l_Lean_Fmt_Error_partialFormatter;
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_a_623_);
return v___x_723_;
}
else
{
lean_object* v_colon_x3f_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_colon_x3f_724_ = l_Lean_Syntax_getArg(v___x_719_, v___x_628_);
v___x_725_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1___closed__3));
lean_inc(v_colon_x3f_724_);
v___x_726_ = l_Lean_Syntax_isOfKind(v_colon_x3f_724_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v_colon_x3f_724_);
lean_dec(v___x_719_);
lean_dec(v___x_631_);
lean_dec(v_guardHypTk_629_);
lean_dec(v_x_621_);
v___x_727_ = l_Lean_Fmt_Error_partialFormatter;
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v_a_623_);
return v___x_728_;
}
else
{
lean_object* v_type_x3f_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_type_x3f_729_ = l_Lean_Syntax_getArg(v___x_719_, v___x_630_);
lean_dec(v___x_719_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_colon_x3f_724_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_type_x3f_729_);
v_colon_x3f_700_ = v___x_730_;
v_type_x3f_701_ = v___x_731_;
v___y_702_ = v_a_622_;
v___y_703_ = v_a_623_;
goto v___jp_699_;
}
}
}
else
{
lean_object* v___x_732_; 
lean_dec(v___x_719_);
v___x_732_ = lean_box(0);
v_colon_x3f_700_ = v___x_732_;
v_type_x3f_701_ = v___x_732_;
v___y_702_ = v_a_622_;
v___y_703_ = v_a_623_;
goto v___jp_699_;
}
v___jp_632_:
{
if (lean_obj_tag(v___y_634_) == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = l_Lean_Fmt_fmtGuardHypLike(v_guardHypTk_629_, v___x_631_, v___y_636_, v___y_635_, v___y_638_, v___x_639_, v___y_633_, v___y_637_);
return v___x_640_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
v_val_641_ = lean_ctor_get(v___y_634_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___y_634_);
if (v_isSharedCheck_649_ == 0)
{
v___x_643_ = v___y_634_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v___y_634_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_val_641_);
v___x_646_ = v_reuseFailAlloc_648_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Fmt_fmtGuardHypLike(v_guardHypTk_629_, v___x_631_, v___y_636_, v___y_635_, v___y_638_, v___x_646_, v___y_633_, v___y_637_);
return v___x_647_;
}
}
}
}
v___jp_650_:
{
if (lean_obj_tag(v___y_653_) == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_box(0);
v___y_633_ = v___y_651_;
v___y_634_ = v___y_652_;
v___y_635_ = v___y_656_;
v___y_636_ = v___y_654_;
v___y_637_ = v___y_655_;
v___y_638_ = v___x_657_;
goto v___jp_632_;
}
else
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_val_658_ = lean_ctor_get(v___y_653_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___y_653_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___y_653_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v___y_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_val_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v___y_633_ = v___y_651_;
v___y_634_ = v___y_652_;
v___y_635_ = v___y_656_;
v___y_636_ = v___y_654_;
v___y_637_ = v___y_655_;
v___y_638_ = v___x_663_;
goto v___jp_632_;
}
}
}
}
v___jp_666_:
{
if (lean_obj_tag(v___y_670_) == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_box(0);
v___y_651_ = v___y_667_;
v___y_652_ = v___y_668_;
v___y_653_ = v___y_669_;
v___y_654_ = v___y_672_;
v___y_655_ = v___y_671_;
v___y_656_ = v___x_673_;
goto v___jp_650_;
}
else
{
lean_object* v_val_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_val_674_ = lean_ctor_get(v___y_670_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___y_670_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___y_670_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_val_674_);
lean_dec(v___y_670_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_val_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
v___y_651_ = v___y_667_;
v___y_652_ = v___y_668_;
v___y_653_ = v___y_669_;
v___y_654_ = v___y_672_;
v___y_655_ = v___y_671_;
v___y_656_ = v___x_679_;
goto v___jp_650_;
}
}
}
}
v___jp_682_:
{
if (lean_obj_tag(v___y_683_) == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_box(0);
v___y_667_ = v___y_687_;
v___y_668_ = v_value_x3f_686_;
v___y_669_ = v_colonEq_x3f_685_;
v___y_670_ = v___y_684_;
v___y_671_ = v___y_688_;
v___y_672_ = v___x_689_;
goto v___jp_666_;
}
else
{
lean_object* v_val_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_val_690_ = lean_ctor_get(v___y_683_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___y_683_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___y_683_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_val_690_);
lean_dec(v___y_683_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_val_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v___y_667_ = v___y_687_;
v___y_668_ = v_value_x3f_686_;
v___y_669_ = v_colonEq_x3f_685_;
v___y_670_ = v___y_684_;
v___y_671_ = v___y_688_;
v___y_672_ = v___x_695_;
goto v___jp_666_;
}
}
}
}
v___jp_699_:
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(3u);
v___x_705_ = l_Lean_Syntax_getArg(v_x_621_, v___x_704_);
lean_dec(v_x_621_);
v___x_706_ = l_Lean_Syntax_isNone(v___x_705_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
lean_inc(v___x_705_);
v___x_707_ = l_Lean_Syntax_matchesNull(v___x_705_, v___x_698_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v___x_705_);
lean_dec(v_type_x3f_701_);
lean_dec(v_colon_x3f_700_);
lean_dec(v___x_631_);
lean_dec(v_guardHypTk_629_);
v___x_708_ = l_Lean_Fmt_Error_partialFormatter;
v___x_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___y_703_);
return v___x_709_;
}
else
{
lean_object* v_colonEq_x3f_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_colonEq_x3f_710_ = l_Lean_Syntax_getArg(v___x_705_, v___x_628_);
v___x_711_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1___closed__1));
lean_inc(v_colonEq_x3f_710_);
v___x_712_ = l_Lean_Syntax_isOfKind(v_colonEq_x3f_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v_colonEq_x3f_710_);
lean_dec(v___x_705_);
lean_dec(v_type_x3f_701_);
lean_dec(v_colon_x3f_700_);
lean_dec(v___x_631_);
lean_dec(v_guardHypTk_629_);
v___x_713_ = l_Lean_Fmt_Error_partialFormatter;
v___x_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___y_703_);
return v___x_714_;
}
else
{
lean_object* v_value_x3f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_value_x3f_715_ = l_Lean_Syntax_getArg(v___x_705_, v___x_630_);
lean_dec(v___x_705_);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v_colonEq_x3f_710_);
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v_value_x3f_715_);
v___y_683_ = v_colon_x3f_700_;
v___y_684_ = v_type_x3f_701_;
v_colonEq_x3f_685_ = v___x_716_;
v_value_x3f_686_ = v___x_717_;
v___y_687_ = v___y_702_;
v___y_688_ = v___y_703_;
goto v___jp_682_;
}
}
}
else
{
lean_object* v___x_718_; 
lean_dec(v___x_705_);
v___x_718_ = lean_box(0);
v___y_683_ = v_colon_x3f_700_;
v___y_684_ = v_type_x3f_701_;
v_colonEq_x3f_685_ = v___x_718_;
v_value_x3f_686_ = v___x_718_;
v___y_687_ = v___y_702_;
v___y_688_ = v___y_703_;
goto v___jp_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardHypConv___boxed(lean_object* v_x_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Fmt_fmtGuardHypConv(v_x_733_, v_a_734_, v_a_735_);
lean_dec_ref(v_a_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1(){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_743_ = l_Lean_Fmt_fmtAttribute;
v___x_744_ = ((lean_object*)(l_Lean_Fmt_fmtGuardHypConv___closed__1));
v___x_745_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___closed__1));
v___x_746_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardHypConv___boxed), 3, 0);
v___x_747_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_743_, v___x_744_, v___x_745_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1___boxed(lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1();
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardCmd(lean_object* v_x_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_Fmt_fmtGuardCmd___closed__1));
lean_inc(v_x_756_);
v___x_760_ = l_Lean_Syntax_isOfKind(v_x_756_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec(v_x_756_);
v___x_761_ = l_Lean_Fmt_Error_partialFormatter;
v___x_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v_a_758_);
return v___x_762_;
}
else
{
lean_object* v___x_763_; lean_object* v_guardTk_764_; lean_object* v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v_guardTk_764_ = l_Lean_Syntax_getArg(v_x_756_, v___x_763_);
v___x_765_ = l_Lean_Fmt_fmt(v_guardTk_764_, v_a_757_, v_a_758_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
v_a_767_ = lean_ctor_get(v___x_765_, 1);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_765_, 2);
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = l_Lean_Syntax_getArg(v_x_756_, v___x_768_);
lean_dec(v_x_756_);
v___x_770_ = l_Lean_Fmt_fmt(v___x_769_, v_a_757_, v_a_767_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_786_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_a_772_ = lean_ctor_get(v___x_770_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_786_ == 0)
{
v___x_774_ = v___x_770_;
v_isShared_775_ = v_isSharedCheck_786_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_786_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_776_ = lean_unsigned_to_nat(2u);
v___x_777_ = lean_mk_empty_array_with_capacity(v___x_776_);
v___x_778_ = lean_array_push(v___x_777_, v_a_766_);
v___x_779_ = lean_array_push(v___x_778_, v_a_771_);
v___x_780_ = 0;
v___x_781_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_781_, 0, v___x_760_);
lean_ctor_set_uint8(v___x_781_, 1, v___x_780_);
lean_ctor_set_uint8(v___x_781_, 2, v___x_780_);
lean_ctor_set_uint8(v___x_781_, 3, v___x_780_);
v___x_782_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_779_, v___x_781_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_782_);
v___x_784_ = v___x_774_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_a_772_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_dec(v_a_766_);
return v___x_770_;
}
}
else
{
lean_dec(v_x_756_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardCmd___boxed(lean_object* v_x_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Fmt_fmtGuardCmd(v_x_787_, v_a_788_, v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1(){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_797_ = l_Lean_Fmt_fmtAttribute;
v___x_798_ = ((lean_object*)(l_Lean_Fmt_fmtGuardCmd___closed__1));
v___x_799_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___closed__1));
v___x_800_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardCmd___boxed), 3, 0);
v___x_801_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_797_, v___x_798_, v___x_799_, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1___boxed(lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1();
return v_res_803_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Guard(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColon___regBuiltin_Lean_Fmt_fmtGuardColon__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardColonEq___regBuiltin_Lean_Fmt_fmtGuardColonEq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardEqual___regBuiltin_Lean_Fmt_fmtGuardEqual__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExpr___regBuiltin_Lean_Fmt_fmtGuardExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprConv___regBuiltin_Lean_Fmt_fmtGuardExprConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardExprCmd___regBuiltin_Lean_Fmt_fmtGuardExprCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTarget___regBuiltin_Lean_Fmt_fmtGuardTarget__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardTargetConv___regBuiltin_Lean_Fmt_fmtGuardTargetConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHyp___regBuiltin_Lean_Fmt_fmtGuardHyp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardHypConv___regBuiltin_Lean_Fmt_fmtGuardHypConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Guard_0__Lean_Fmt_fmtGuardCmd___regBuiltin_Lean_Fmt_fmtGuardCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Guard(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Guard(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Guard(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Guard(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Guard(builtin);
}
#ifdef __cplusplus
}
#endif
