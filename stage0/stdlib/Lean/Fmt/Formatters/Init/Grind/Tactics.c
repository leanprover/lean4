// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Grind.Tactics
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Grind.Tactics import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSimpLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGrindTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__3_value),LEAN_SCALAR_PTR_LITERAL(150, 98, 0, 78, 28, 79, 28, 100)}};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtGrindTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtGrindTactic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtGrindTactic___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__9_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__9_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__9_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__7_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTactic___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__9_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__8_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l_Lean_Fmt_fmtGrindTactic___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtGrindTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(125, 182, 165, 136, 113, 83, 67, 114)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindTraceTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindTrace"};
static const lean_object* l_Lean_Fmt_fmtGrindTraceTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindTraceTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindTraceTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTraceTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTraceTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTraceTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTraceTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindTraceTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindTraceTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindTraceTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 245, 239, 189, 189, 113, 196, 115)}};
static const lean_object* l_Lean_Fmt_fmtGrindTraceTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindTraceTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTraceTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTraceTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindTraceTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 77, 139, 109, 168, 248, 4, 24)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l_Lean_Fmt_fmtSymTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 232, 82, 57, 183, 116, 37)}};
static const lean_object* l_Lean_Fmt_fmtSymTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtSymTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 242, 38, 223, 249, 50, 110, 21)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCutsat_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCutsat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCutsat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cutsat"};
static const lean_object* l_Lean_Fmt_fmtCutsat___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCutsat___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCutsat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCutsat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCutsat___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCutsat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCutsat___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtCutsat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCutsat___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtCutsat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 143, 41, 132, 162, 171, 243, 34)}};
static const lean_object* l_Lean_Fmt_fmtCutsat___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCutsat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCutsat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCutsat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtCutsat"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 149, 184, 154, 25, 194, 186, 26)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLiaTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Fmt_fmtLiaTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLiaTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLiaTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtLiaTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLiaTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLiaTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 74, 44, 139, 89, 35, 186, 8)}};
static const lean_object* l_Lean_Fmt_fmtLiaTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLiaTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtLiaTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 33, 88, 85, 206, 144, 141, 236)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindOrder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grind_order"};
static const lean_object* l_Lean_Fmt_fmtGrindOrder___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindOrder___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindOrder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindOrder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindOrder___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindOrder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindOrder___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindOrder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindOrder___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 44, 144, 70, 207, 54, 125, 88)}};
static const lean_object* l_Lean_Fmt_fmtGrindOrder___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindOrder___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindOrder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindOrder___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtGrindOrder"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 91, 156, 131, 214, 45, 86, 156)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindLinarithTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_linarith"};
static const lean_object* l_Lean_Fmt_fmtGrindLinarithTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindLinarithTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindLinarithTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLinarithTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLinarithTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLinarithTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLinarithTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLinarithTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLinarithTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindLinarithTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 70, 60, 37, 53, 143, 147, 85)}};
static const lean_object* l_Lean_Fmt_fmtGrindLinarithTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindLinarithTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLinarithTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLinarithTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtGrindLinarithTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 48, 60, 176, 153, 23, 33, 247)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrobner___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grobner"};
static const lean_object* l_Lean_Fmt_fmtGrobner___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrobner___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrobner___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrobner___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrobner___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrobner___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrobner___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrobner___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrobner___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrobner___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 188, 100, 211, 106, 33, 144, 166)}};
static const lean_object* l_Lean_Fmt_fmtGrobner___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrobner___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrobner(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrobner___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtGrobner"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 15, 14, 18, 6, 212, 55, 101)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTactic(lean_object* v_x_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___y_28_; lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v___y_31_; lean_object* v___y_32_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__4));
lean_inc(v_x_24_);
v___x_46_ = l_Lean_Syntax_isOfKind(v_x_24_, v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_x_24_);
v___x_47_ = l_Lean_Fmt_Error_partialFormatter;
v___x_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v_a_26_);
return v___x_48_;
}
else
{
lean_object* v___x_49_; lean_object* v_cfg_50_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___y_58_; lean_object* v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v_cfg_50_ = l_Lean_Syntax_getArg(v_x_24_, v___x_49_);
v___x_79_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__6));
lean_inc(v_cfg_50_);
v___x_80_ = l_Lean_Syntax_isOfKind(v_cfg_50_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_cfg_50_);
lean_dec(v_x_24_);
v___x_81_ = l_Lean_Fmt_Error_partialFormatter;
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_26_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v_grindTk_84_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v_arrowTk_x3f_90_; lean_object* v_seq_x3f_91_; lean_object* v___y_92_; lean_object* v___y_93_; lean_object* v___x_105_; lean_object* v___y_107_; lean_object* v_lbTk_x3f_108_; lean_object* v_args_x3f_109_; lean_object* v_rbTk_x3f_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v_only_x3f_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v_grindTk_84_ = l_Lean_Syntax_getArg(v_x_24_, v___x_83_);
v___x_105_ = lean_unsigned_to_nat(2u);
v___x_146_ = l_Lean_Syntax_getArg(v_x_24_, v___x_105_);
v___x_147_ = l_Lean_Syntax_isNone(v___x_146_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; 
lean_inc(v___x_146_);
v___x_148_ = l_Lean_Syntax_matchesNull(v___x_146_, v___x_49_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v___x_146_);
lean_dec(v_grindTk_84_);
lean_dec(v_cfg_50_);
lean_dec(v_x_24_);
v___x_149_ = l_Lean_Fmt_Error_partialFormatter;
v___x_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_a_26_);
return v___x_150_;
}
else
{
lean_object* v_only_x3f_151_; lean_object* v___x_152_; 
v_only_x3f_151_ = l_Lean_Syntax_getArg(v___x_146_, v___x_83_);
lean_dec(v___x_146_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_only_x3f_151_);
v_only_x3f_129_ = v___x_152_;
v___y_130_ = v_a_25_;
v___y_131_ = v_a_26_;
goto v___jp_128_;
}
}
else
{
lean_object* v___x_153_; 
lean_dec(v___x_146_);
v___x_153_ = lean_box(0);
v_only_x3f_129_ = v___x_153_;
v___y_130_ = v_a_25_;
v___y_131_ = v_a_26_;
goto v___jp_128_;
}
v___jp_85_:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_49_);
v___x_95_ = lean_array_push(v___x_94_, v_grindTk_84_);
v___x_96_ = lean_box(0);
if (lean_obj_tag(v___y_88_) == 0)
{
v___y_52_ = v___x_95_;
v___y_53_ = v___y_87_;
v___y_54_ = v___y_86_;
v___y_55_ = v_arrowTk_x3f_90_;
v___y_56_ = v___y_89_;
v___y_57_ = v___x_96_;
v___y_58_ = v_seq_x3f_91_;
v___y_59_ = v___y_92_;
v___y_60_ = v___y_93_;
v___y_61_ = v___x_96_;
goto v___jp_51_;
}
else
{
lean_object* v_val_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_val_97_ = lean_ctor_get(v___y_88_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___y_88_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___y_88_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_val_97_);
lean_dec(v___y_88_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_val_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
v___y_52_ = v___x_95_;
v___y_53_ = v___y_87_;
v___y_54_ = v___y_86_;
v___y_55_ = v_arrowTk_x3f_90_;
v___y_56_ = v___y_89_;
v___y_57_ = v___x_96_;
v___y_58_ = v_seq_x3f_91_;
v___y_59_ = v___y_92_;
v___y_60_ = v___y_93_;
v___y_61_ = v___x_102_;
goto v___jp_51_;
}
}
}
}
v___jp_106_:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(4u);
v___x_114_ = l_Lean_Syntax_getArg(v_x_24_, v___x_113_);
lean_dec(v_x_24_);
v___x_115_ = l_Lean_Syntax_isNone(v___x_114_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; 
lean_inc(v___x_114_);
v___x_116_ = l_Lean_Syntax_matchesNull(v___x_114_, v___x_105_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v___x_114_);
lean_dec(v_rbTk_x3f_110_);
lean_dec(v_args_x3f_109_);
lean_dec(v_lbTk_x3f_108_);
lean_dec(v___y_107_);
lean_dec(v_grindTk_84_);
lean_dec(v_cfg_50_);
v___x_117_ = l_Lean_Fmt_Error_partialFormatter;
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___y_112_);
return v___x_118_;
}
else
{
lean_object* v_seq_x3f_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_seq_x3f_119_ = l_Lean_Syntax_getArg(v___x_114_, v___x_49_);
v___x_120_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__9));
lean_inc(v_seq_x3f_119_);
v___x_121_ = l_Lean_Syntax_isOfKind(v_seq_x3f_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_seq_x3f_119_);
lean_dec(v___x_114_);
lean_dec(v_rbTk_x3f_110_);
lean_dec(v_args_x3f_109_);
lean_dec(v_lbTk_x3f_108_);
lean_dec(v___y_107_);
lean_dec(v_grindTk_84_);
lean_dec(v_cfg_50_);
v___x_122_ = l_Lean_Fmt_Error_partialFormatter;
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___y_112_);
return v___x_123_;
}
else
{
lean_object* v_arrowTk_x3f_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_arrowTk_x3f_124_ = l_Lean_Syntax_getArg(v___x_114_, v___x_83_);
lean_dec(v___x_114_);
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v_arrowTk_x3f_124_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v_seq_x3f_119_);
v___y_86_ = v_lbTk_x3f_108_;
v___y_87_ = v_rbTk_x3f_110_;
v___y_88_ = v_args_x3f_109_;
v___y_89_ = v___y_107_;
v_arrowTk_x3f_90_ = v___x_125_;
v_seq_x3f_91_ = v___x_126_;
v___y_92_ = v___y_111_;
v___y_93_ = v___y_112_;
goto v___jp_85_;
}
}
}
else
{
lean_object* v___x_127_; 
lean_dec(v___x_114_);
v___x_127_ = lean_box(0);
v___y_86_ = v_lbTk_x3f_108_;
v___y_87_ = v_rbTk_x3f_110_;
v___y_88_ = v_args_x3f_109_;
v___y_89_ = v___y_107_;
v_arrowTk_x3f_90_ = v___x_127_;
v_seq_x3f_91_ = v___x_127_;
v___y_92_ = v___y_111_;
v___y_93_ = v___y_112_;
goto v___jp_85_;
}
}
v___jp_128_:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = lean_unsigned_to_nat(3u);
v___x_133_ = l_Lean_Syntax_getArg(v_x_24_, v___x_132_);
v___x_134_ = l_Lean_Syntax_isNone(v___x_133_);
if (v___x_134_ == 0)
{
uint8_t v___x_135_; 
lean_inc(v___x_133_);
v___x_135_ = l_Lean_Syntax_matchesNull(v___x_133_, v___x_132_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v___x_133_);
lean_dec(v_only_x3f_129_);
lean_dec(v_grindTk_84_);
lean_dec(v_cfg_50_);
lean_dec(v_x_24_);
v___x_136_ = l_Lean_Fmt_Error_partialFormatter;
v___x_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___y_131_);
return v___x_137_;
}
else
{
lean_object* v_lbTk_x3f_138_; lean_object* v___x_139_; lean_object* v_rbTk_x3f_140_; lean_object* v_args_x3f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_lbTk_x3f_138_ = l_Lean_Syntax_getArg(v___x_133_, v___x_83_);
v___x_139_ = l_Lean_Syntax_getArg(v___x_133_, v___x_49_);
v_rbTk_x3f_140_ = l_Lean_Syntax_getArg(v___x_133_, v___x_105_);
lean_dec(v___x_133_);
v_args_x3f_141_ = l_Lean_Syntax_getArgs(v___x_139_);
lean_dec(v___x_139_);
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v_lbTk_x3f_138_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v_args_x3f_141_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v_rbTk_x3f_140_);
v___y_107_ = v_only_x3f_129_;
v_lbTk_x3f_108_ = v___x_142_;
v_args_x3f_109_ = v___x_143_;
v_rbTk_x3f_110_ = v___x_144_;
v___y_111_ = v___y_130_;
v___y_112_ = v___y_131_;
goto v___jp_106_;
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v___y_107_ = v_only_x3f_129_;
v_lbTk_x3f_108_ = v___x_145_;
v_args_x3f_109_ = v___x_145_;
v_rbTk_x3f_110_ = v___x_145_;
v___y_111_ = v___y_130_;
v___y_112_ = v___y_131_;
goto v___jp_106_;
}
}
}
v___jp_51_:
{
lean_object* v___x_62_; 
lean_inc(v___y_57_);
v___x_62_ = l_Lean_Fmt_fmtSimpLike(v___y_52_, v_cfg_50_, v___y_57_, v___y_56_, v___y_54_, v___y_61_, v___y_53_, v___y_57_, v___y_59_, v___y_60_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v_a_64_; lean_object* v___x_65_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
v_a_64_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_62_, 2);
v___x_65_ = l_Lean_Fmt_fmt_x3f(v___y_55_, v___y_59_, v_a_64_);
if (lean_obj_tag(v___x_65_) == 0)
{
if (lean_obj_tag(v___y_58_) == 0)
{
lean_object* v_a_66_; lean_object* v_a_67_; lean_object* v___x_68_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
v_a_67_ = lean_ctor_get(v___x_65_, 1);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_65_, 2);
v___x_68_ = lean_box(0);
v___y_28_ = v_a_67_;
v___y_29_ = v_a_66_;
v___y_30_ = v___y_59_;
v___y_31_ = v_a_63_;
v___y_32_ = v___x_68_;
goto v___jp_27_;
}
else
{
lean_object* v_a_69_; lean_object* v_a_70_; lean_object* v_val_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
v_a_69_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_69_);
v_a_70_ = lean_ctor_get(v___x_65_, 1);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_65_, 2);
v_val_71_ = lean_ctor_get(v___y_58_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___y_58_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___y_58_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_val_71_);
lean_dec(v___y_58_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_val_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
v___y_28_ = v_a_70_;
v___y_29_ = v_a_69_;
v___y_30_ = v___y_59_;
v___y_31_ = v_a_63_;
v___y_32_ = v___x_76_;
goto v___jp_27_;
}
}
}
}
else
{
lean_dec(v_a_63_);
lean_dec(v___y_58_);
return v___x_65_;
}
}
else
{
lean_dec(v___y_58_);
lean_dec(v___y_55_);
return v___x_62_;
}
}
}
v___jp_27_:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Fmt_fmt_x3f(v___y_32_, v___y_30_, v___y_28_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_44_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_a_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_44_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
uint8_t v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_39_ = 0;
v___x_40_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___y_31_, v___y_29_, v_a_34_, v___x_39_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_40_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_a_35_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
else
{
lean_dec_ref(v___y_31_);
lean_dec_ref(v___y_29_);
return v___x_33_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTactic___boxed(lean_object* v_x_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Fmt_fmtGrindTactic(v_x_154_, v_a_155_, v_a_156_);
lean_dec_ref(v_a_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1(){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = l_Lean_Fmt_fmtAttribute;
v___x_166_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__4));
v___x_167_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___closed__2));
v___x_168_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindTactic___boxed), 3, 0);
v___x_169_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_165_, v___x_166_, v___x_167_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1___boxed(lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1();
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTraceTactic(lean_object* v_x_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTraceTactic___closed__1));
lean_inc(v_x_178_);
v___x_182_ = l_Lean_Syntax_isOfKind(v_x_178_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_x_178_);
v___x_183_ = l_Lean_Fmt_Error_partialFormatter;
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_180_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v_cfg_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v_cfg_186_ = l_Lean_Syntax_getArg(v_x_178_, v___x_185_);
v___x_187_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__6));
lean_inc(v_cfg_186_);
v___x_188_ = l_Lean_Syntax_isOfKind(v_cfg_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_cfg_186_);
lean_dec(v_x_178_);
v___x_189_ = l_Lean_Fmt_Error_partialFormatter;
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_180_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v_grindTk_192_; lean_object* v___y_194_; lean_object* v_lbTk_x3f_195_; lean_object* v_args_x3f_196_; lean_object* v_rbTk_x3f_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___x_213_; lean_object* v_only_x3f_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v_grindTk_192_ = l_Lean_Syntax_getArg(v_x_178_, v___x_191_);
v___x_213_ = lean_unsigned_to_nat(2u);
v___x_232_ = l_Lean_Syntax_getArg(v_x_178_, v___x_213_);
v___x_233_ = l_Lean_Syntax_isNone(v___x_232_);
if (v___x_233_ == 0)
{
uint8_t v___x_234_; 
lean_inc(v___x_232_);
v___x_234_ = l_Lean_Syntax_matchesNull(v___x_232_, v___x_185_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v___x_232_);
lean_dec(v_grindTk_192_);
lean_dec(v_cfg_186_);
lean_dec(v_x_178_);
v___x_235_ = l_Lean_Fmt_Error_partialFormatter;
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_a_180_);
return v___x_236_;
}
else
{
lean_object* v_only_x3f_237_; lean_object* v___x_238_; 
v_only_x3f_237_ = l_Lean_Syntax_getArg(v___x_232_, v___x_191_);
lean_dec(v___x_232_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v_only_x3f_237_);
v_only_x3f_215_ = v___x_238_;
v___y_216_ = v_a_179_;
v___y_217_ = v_a_180_;
goto v___jp_214_;
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v___x_232_);
v___x_239_ = lean_box(0);
v_only_x3f_215_ = v___x_239_;
v___y_216_ = v_a_179_;
v___y_217_ = v_a_180_;
goto v___jp_214_;
}
v___jp_193_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_mk_empty_array_with_capacity(v___x_185_);
v___x_201_ = lean_array_push(v___x_200_, v_grindTk_192_);
v___x_202_ = lean_box(0);
if (lean_obj_tag(v_args_x3f_196_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Fmt_fmtSimpLike(v___x_201_, v_cfg_186_, v___x_202_, v___y_194_, v_lbTk_x3f_195_, v___x_202_, v_rbTk_x3f_197_, v___x_202_, v___y_198_, v___y_199_);
return v___x_203_;
}
else
{
lean_object* v_val_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_val_204_ = lean_ctor_get(v_args_x3f_196_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_args_x3f_196_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v_args_x3f_196_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_val_204_);
lean_dec(v_args_x3f_196_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_val_204_);
v___x_209_ = v_reuseFailAlloc_211_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Fmt_fmtSimpLike(v___x_201_, v_cfg_186_, v___x_202_, v___y_194_, v_lbTk_x3f_195_, v___x_209_, v_rbTk_x3f_197_, v___x_202_, v___y_198_, v___y_199_);
return v___x_210_;
}
}
}
}
v___jp_214_:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(3u);
v___x_219_ = l_Lean_Syntax_getArg(v_x_178_, v___x_218_);
lean_dec(v_x_178_);
v___x_220_ = l_Lean_Syntax_isNone(v___x_219_);
if (v___x_220_ == 0)
{
uint8_t v___x_221_; 
lean_inc(v___x_219_);
v___x_221_ = l_Lean_Syntax_matchesNull(v___x_219_, v___x_218_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v___x_219_);
lean_dec(v_only_x3f_215_);
lean_dec(v_grindTk_192_);
lean_dec(v_cfg_186_);
v___x_222_ = l_Lean_Fmt_Error_partialFormatter;
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___y_217_);
return v___x_223_;
}
else
{
lean_object* v_lbTk_x3f_224_; lean_object* v___x_225_; lean_object* v_rbTk_x3f_226_; lean_object* v_args_x3f_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_lbTk_x3f_224_ = l_Lean_Syntax_getArg(v___x_219_, v___x_191_);
v___x_225_ = l_Lean_Syntax_getArg(v___x_219_, v___x_185_);
v_rbTk_x3f_226_ = l_Lean_Syntax_getArg(v___x_219_, v___x_213_);
lean_dec(v___x_219_);
v_args_x3f_227_ = l_Lean_Syntax_getArgs(v___x_225_);
lean_dec(v___x_225_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_lbTk_x3f_224_);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v_args_x3f_227_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_rbTk_x3f_226_);
v___y_194_ = v_only_x3f_215_;
v_lbTk_x3f_195_ = v___x_228_;
v_args_x3f_196_ = v___x_229_;
v_rbTk_x3f_197_ = v___x_230_;
v___y_198_ = v___y_216_;
v___y_199_ = v___y_217_;
goto v___jp_193_;
}
}
else
{
lean_object* v___x_231_; 
lean_dec(v___x_219_);
v___x_231_ = lean_box(0);
v___y_194_ = v_only_x3f_215_;
v_lbTk_x3f_195_ = v___x_231_;
v_args_x3f_196_ = v___x_231_;
v_rbTk_x3f_197_ = v___x_231_;
v___y_198_ = v___y_216_;
v___y_199_ = v___y_217_;
goto v___jp_193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindTraceTactic___boxed(lean_object* v_x_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Fmt_fmtGrindTraceTactic(v_x_240_, v_a_241_, v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_250_ = l_Lean_Fmt_fmtAttribute;
v___x_251_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTraceTactic___closed__1));
v___x_252_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___closed__1));
v___x_253_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindTraceTactic___boxed), 3, 0);
v___x_254_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_250_, v___x_251_, v___x_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1___boxed(lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymTactic(lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Fmt_fmtSymTactic___closed__1));
lean_inc(v_x_263_);
v___x_267_ = l_Lean_Syntax_isOfKind(v_x_263_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_x_263_);
v___x_268_ = l_Lean_Fmt_Error_partialFormatter;
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_a_265_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v_cfg_271_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v_cfg_271_ = l_Lean_Syntax_getArg(v_x_263_, v___x_270_);
v___x_301_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__6));
lean_inc(v_cfg_271_);
v___x_302_ = l_Lean_Syntax_isOfKind(v_cfg_271_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_cfg_271_);
lean_dec(v_x_263_);
v___x_303_ = l_Lean_Fmt_Error_partialFormatter;
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v_a_265_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v_symTk_306_; lean_object* v___y_308_; lean_object* v_lbTk_x3f_309_; lean_object* v_args_x3f_310_; lean_object* v_rbTk_x3f_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___x_333_; lean_object* v_only_x3f_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v_symTk_306_ = l_Lean_Syntax_getArg(v_x_263_, v___x_305_);
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_352_ = l_Lean_Syntax_getArg(v_x_263_, v___x_333_);
v___x_353_ = l_Lean_Syntax_isNone(v___x_352_);
if (v___x_353_ == 0)
{
uint8_t v___x_354_; 
lean_inc(v___x_352_);
v___x_354_ = l_Lean_Syntax_matchesNull(v___x_352_, v___x_270_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v___x_352_);
lean_dec(v_symTk_306_);
lean_dec(v_cfg_271_);
lean_dec(v_x_263_);
v___x_355_ = l_Lean_Fmt_Error_partialFormatter;
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_a_265_);
return v___x_356_;
}
else
{
lean_object* v_only_x3f_357_; lean_object* v___x_358_; 
v_only_x3f_357_ = l_Lean_Syntax_getArg(v___x_352_, v___x_305_);
lean_dec(v___x_352_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v_only_x3f_357_);
v_only_x3f_335_ = v___x_358_;
v___y_336_ = v_a_264_;
v___y_337_ = v_a_265_;
goto v___jp_334_;
}
}
else
{
lean_object* v___x_359_; 
lean_dec(v___x_352_);
v___x_359_ = lean_box(0);
v_only_x3f_335_ = v___x_359_;
v___y_336_ = v_a_264_;
v___y_337_ = v_a_265_;
goto v___jp_334_;
}
v___jp_307_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_314_ = lean_unsigned_to_nat(5u);
v___x_315_ = l_Lean_Syntax_getArg(v_x_263_, v___x_314_);
v___x_316_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__9));
lean_inc(v___x_315_);
v___x_317_ = l_Lean_Syntax_isOfKind(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v___x_315_);
lean_dec(v_rbTk_x3f_311_);
lean_dec(v_args_x3f_310_);
lean_dec(v_lbTk_x3f_309_);
lean_dec(v___y_308_);
lean_dec(v_symTk_306_);
lean_dec(v_cfg_271_);
lean_dec(v_x_263_);
v___x_318_ = l_Lean_Fmt_Error_partialFormatter;
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___y_313_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v_arrowTk_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_320_ = lean_unsigned_to_nat(4u);
v_arrowTk_321_ = l_Lean_Syntax_getArg(v_x_263_, v___x_320_);
lean_dec(v_x_263_);
v___x_322_ = lean_mk_empty_array_with_capacity(v___x_270_);
v___x_323_ = lean_array_push(v___x_322_, v_symTk_306_);
v___x_324_ = lean_box(0);
if (lean_obj_tag(v_args_x3f_310_) == 0)
{
v___y_273_ = v___y_312_;
v___y_274_ = v___x_323_;
v___y_275_ = v_arrowTk_321_;
v___y_276_ = v_rbTk_x3f_311_;
v___y_277_ = v___x_324_;
v___y_278_ = v___y_308_;
v___y_279_ = v___x_315_;
v___y_280_ = v___y_313_;
v___y_281_ = v_lbTk_x3f_309_;
v___y_282_ = v___x_324_;
goto v___jp_272_;
}
else
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_val_325_ = lean_ctor_get(v_args_x3f_310_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_args_x3f_310_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v_args_x3f_310_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v_args_x3f_310_);
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
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_val_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
v___y_273_ = v___y_312_;
v___y_274_ = v___x_323_;
v___y_275_ = v_arrowTk_321_;
v___y_276_ = v_rbTk_x3f_311_;
v___y_277_ = v___x_324_;
v___y_278_ = v___y_308_;
v___y_279_ = v___x_315_;
v___y_280_ = v___y_313_;
v___y_281_ = v_lbTk_x3f_309_;
v___y_282_ = v___x_330_;
goto v___jp_272_;
}
}
}
}
}
v___jp_334_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_unsigned_to_nat(3u);
v___x_339_ = l_Lean_Syntax_getArg(v_x_263_, v___x_338_);
v___x_340_ = l_Lean_Syntax_isNone(v___x_339_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
lean_inc(v___x_339_);
v___x_341_ = l_Lean_Syntax_matchesNull(v___x_339_, v___x_338_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v___x_339_);
lean_dec(v_only_x3f_335_);
lean_dec(v_symTk_306_);
lean_dec(v_cfg_271_);
lean_dec(v_x_263_);
v___x_342_ = l_Lean_Fmt_Error_partialFormatter;
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___y_337_);
return v___x_343_;
}
else
{
lean_object* v_lbTk_x3f_344_; lean_object* v___x_345_; lean_object* v_rbTk_x3f_346_; lean_object* v_args_x3f_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_lbTk_x3f_344_ = l_Lean_Syntax_getArg(v___x_339_, v___x_305_);
v___x_345_ = l_Lean_Syntax_getArg(v___x_339_, v___x_270_);
v_rbTk_x3f_346_ = l_Lean_Syntax_getArg(v___x_339_, v___x_333_);
lean_dec(v___x_339_);
v_args_x3f_347_ = l_Lean_Syntax_getArgs(v___x_345_);
lean_dec(v___x_345_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v_lbTk_x3f_344_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_args_x3f_347_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_rbTk_x3f_346_);
v___y_308_ = v_only_x3f_335_;
v_lbTk_x3f_309_ = v___x_348_;
v_args_x3f_310_ = v___x_349_;
v_rbTk_x3f_311_ = v___x_350_;
v___y_312_ = v___y_336_;
v___y_313_ = v___y_337_;
goto v___jp_307_;
}
}
else
{
lean_object* v___x_351_; 
lean_dec(v___x_339_);
v___x_351_ = lean_box(0);
v___y_308_ = v_only_x3f_335_;
v_lbTk_x3f_309_ = v___x_351_;
v_args_x3f_310_ = v___x_351_;
v_rbTk_x3f_311_ = v___x_351_;
v___y_312_ = v___y_336_;
v___y_313_ = v___y_337_;
goto v___jp_307_;
}
}
}
v___jp_272_:
{
lean_object* v___x_283_; 
lean_inc(v___y_277_);
v___x_283_ = l_Lean_Fmt_fmtSimpLike(v___y_274_, v_cfg_271_, v___y_277_, v___y_278_, v___y_281_, v___y_282_, v___y_276_, v___y_277_, v___y_273_, v___y_280_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v_a_285_; lean_object* v___x_286_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
v_a_285_ = lean_ctor_get(v___x_283_, 1);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_283_, 2);
v___x_286_ = l_Lean_Fmt_fmt(v___y_275_, v___y_273_, v_a_285_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v_a_288_; lean_object* v___x_289_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
v_a_288_ = lean_ctor_get(v___x_286_, 1);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_286_, 2);
v___x_289_ = l_Lean_Fmt_fmt(v___y_279_, v___y_273_, v_a_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_300_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_a_291_ = lean_ctor_get(v___x_289_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_300_ == 0)
{
v___x_293_ = v___x_289_;
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_295_ = 0;
v___x_296_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_284_, v_a_287_, v_a_290_, v___x_295_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_296_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_a_291_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_dec(v_a_287_);
lean_dec(v_a_284_);
return v___x_289_;
}
}
else
{
lean_dec(v_a_284_);
lean_dec(v___y_279_);
return v___x_286_;
}
}
else
{
lean_dec(v___y_279_);
lean_dec(v___y_275_);
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymTactic___boxed(lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Fmt_fmtSymTactic(v_x_360_, v_a_361_, v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1(){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_370_ = l_Lean_Fmt_fmtAttribute;
v___x_371_ = ((lean_object*)(l_Lean_Fmt_fmtSymTactic___closed__1));
v___x_372_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___closed__1));
v___x_373_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymTactic___boxed), 3, 0);
v___x_374_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_370_, v___x_371_, v___x_372_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1___boxed(lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1();
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCutsat_spec__0(size_t v_sz_377_, size_t v_i_378_, lean_object* v_bs_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_lt(v_i_378_, v_sz_377_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_bs_379_);
lean_ctor_set(v___x_383_, 1, v___y_381_);
return v___x_383_;
}
else
{
lean_object* v_v_384_; lean_object* v___x_385_; 
v_v_384_ = lean_array_uget_borrowed(v_bs_379_, v_i_378_);
lean_inc(v_v_384_);
v___x_385_ = l_Lean_Fmt_fmt(v_v_384_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v_bs_x27_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
v_a_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_385_, 2);
v___x_388_ = lean_unsigned_to_nat(0u);
v_bs_x27_389_ = lean_array_uset(v_bs_379_, v_i_378_, v___x_388_);
v___x_390_ = ((size_t)1ULL);
v___x_391_ = lean_usize_add(v_i_378_, v___x_390_);
v___x_392_ = lean_array_uset(v_bs_x27_389_, v_i_378_, v_a_386_);
v_i_378_ = v___x_391_;
v_bs_379_ = v___x_392_;
v___y_381_ = v_a_387_;
goto _start;
}
else
{
lean_object* v_a_394_; lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_bs_379_);
v_a_394_ = lean_ctor_get(v___x_385_, 0);
v_a_395_ = lean_ctor_get(v___x_385_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_385_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_inc(v_a_394_);
lean_dec(v___x_385_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_394_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCutsat_spec__0___boxed(lean_object* v_sz_403_, lean_object* v_i_404_, lean_object* v_bs_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_403_);
lean_dec(v_sz_403_);
v_i_boxed_409_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCutsat_spec__0(v_sz_boxed_408_, v_i_boxed_409_, v_bs_405_, v___y_406_, v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCutsat(lean_object* v_x_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Fmt_fmtCutsat___closed__1));
lean_inc(v_x_417_);
v___x_421_ = l_Lean_Syntax_isOfKind(v_x_417_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_x_417_);
v___x_422_ = l_Lean_Fmt_Error_partialFormatter;
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_a_419_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v_cfg_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v_cfg_425_ = l_Lean_Syntax_getArg(v_x_417_, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__6));
lean_inc(v_cfg_425_);
v___x_427_ = l_Lean_Syntax_isOfKind(v_cfg_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v_cfg_425_);
lean_dec(v_x_417_);
v___x_428_ = l_Lean_Fmt_Error_partialFormatter;
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_a_419_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v_tk_431_; lean_object* v___x_432_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v_tk_431_ = l_Lean_Syntax_getArg(v_x_417_, v___x_430_);
lean_dec(v_x_417_);
v___x_432_ = l_Lean_Fmt_fmt(v_tk_431_, v_a_418_, v_a_419_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
v_a_434_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_432_, 2);
v___x_435_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_425_, v_a_434_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v_a_437_; size_t v_sz_438_; size_t v___x_439_; lean_object* v___x_440_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
v_a_437_ = lean_ctor_get(v___x_435_, 1);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_435_, 2);
v_sz_438_ = lean_array_size(v_a_436_);
v___x_439_ = ((size_t)0ULL);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCutsat_spec__0(v_sz_438_, v___x_439_, v_a_436_, v_a_418_, v_a_437_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_455_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_a_442_ = lean_ctor_get(v___x_440_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_455_ == 0)
{
v___x_444_ = v___x_440_;
v_isShared_445_ = v_isSharedCheck_455_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_455_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_424_);
v___x_447_ = lean_array_push(v___x_446_, v_a_433_);
v___x_448_ = l_Array_append___redArg(v___x_447_, v_a_441_);
lean_dec(v_a_441_);
v___x_449_ = 0;
v___x_450_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_450_, 0, v___x_427_);
lean_ctor_set_uint8(v___x_450_, 1, v___x_449_);
lean_ctor_set_uint8(v___x_450_, 2, v___x_449_);
lean_ctor_set_uint8(v___x_450_, 3, v___x_449_);
v___x_451_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_448_, v___x_450_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_451_);
v___x_453_ = v___x_444_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_a_442_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_433_);
v_a_456_ = lean_ctor_get(v___x_440_, 0);
v_a_457_ = lean_ctor_get(v___x_440_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_440_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_inc(v_a_456_);
lean_dec(v___x_440_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_a_433_);
v_a_465_ = lean_ctor_get(v___x_435_, 0);
v_a_466_ = lean_ctor_get(v___x_435_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_435_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_inc(v_a_465_);
lean_dec(v___x_435_);
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
lean_dec(v_cfg_425_);
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCutsat___boxed(lean_object* v_x_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Fmt_fmtCutsat(v_x_474_, v_a_475_, v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1(){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = l_Lean_Fmt_fmtAttribute;
v___x_485_ = ((lean_object*)(l_Lean_Fmt_fmtCutsat___closed__1));
v___x_486_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___closed__1));
v___x_487_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCutsat___boxed), 3, 0);
v___x_488_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_484_, v___x_485_, v___x_486_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1___boxed(lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1();
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaTactic(lean_object* v_x_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Fmt_fmtLiaTactic___closed__1));
lean_inc(v_x_497_);
v___x_501_ = l_Lean_Syntax_isOfKind(v_x_497_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_x_497_);
v___x_502_ = l_Lean_Fmt_Error_partialFormatter;
v___x_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_a_499_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v_cfg_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v_cfg_505_ = l_Lean_Syntax_getArg(v_x_497_, v___x_504_);
v___x_506_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__6));
lean_inc(v_cfg_505_);
v___x_507_ = l_Lean_Syntax_isOfKind(v_cfg_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_cfg_505_);
lean_dec(v_x_497_);
v___x_508_ = l_Lean_Fmt_Error_partialFormatter;
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_a_499_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v_tk_511_; lean_object* v_lbTk_x3f_513_; lean_object* v_args_x3f_514_; lean_object* v_rbTk_x3f_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v_tk_511_ = l_Lean_Syntax_getArg(v_x_497_, v___x_510_);
v___x_531_ = lean_unsigned_to_nat(2u);
v___x_532_ = l_Lean_Syntax_getArg(v_x_497_, v___x_531_);
lean_dec(v_x_497_);
v___x_533_ = l_Lean_Syntax_isNone(v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_532_);
v___x_535_ = l_Lean_Syntax_matchesNull(v___x_532_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v___x_532_);
lean_dec(v_tk_511_);
lean_dec(v_cfg_505_);
v___x_536_ = l_Lean_Fmt_Error_partialFormatter;
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_a_499_);
return v___x_537_;
}
else
{
lean_object* v_lbTk_x3f_538_; lean_object* v___x_539_; lean_object* v_rbTk_x3f_540_; lean_object* v_args_x3f_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_lbTk_x3f_538_ = l_Lean_Syntax_getArg(v___x_532_, v___x_510_);
v___x_539_ = l_Lean_Syntax_getArg(v___x_532_, v___x_504_);
v_rbTk_x3f_540_ = l_Lean_Syntax_getArg(v___x_532_, v___x_531_);
lean_dec(v___x_532_);
v_args_x3f_541_ = l_Lean_Syntax_getArgs(v___x_539_);
lean_dec(v___x_539_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_lbTk_x3f_538_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_args_x3f_541_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_rbTk_x3f_540_);
v_lbTk_x3f_513_ = v___x_542_;
v_args_x3f_514_ = v___x_543_;
v_rbTk_x3f_515_ = v___x_544_;
v___y_516_ = v_a_498_;
v___y_517_ = v_a_499_;
goto v___jp_512_;
}
}
else
{
lean_object* v___x_545_; 
lean_dec(v___x_532_);
v___x_545_ = lean_box(0);
v_lbTk_x3f_513_ = v___x_545_;
v_args_x3f_514_ = v___x_545_;
v_rbTk_x3f_515_ = v___x_545_;
v___y_516_ = v_a_498_;
v___y_517_ = v_a_499_;
goto v___jp_512_;
}
v___jp_512_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_mk_empty_array_with_capacity(v___x_504_);
v___x_519_ = lean_array_push(v___x_518_, v_tk_511_);
v___x_520_ = lean_box(0);
if (lean_obj_tag(v_args_x3f_514_) == 0)
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Fmt_fmtSimpLike(v___x_519_, v_cfg_505_, v___x_520_, v___x_520_, v_lbTk_x3f_513_, v___x_520_, v_rbTk_x3f_515_, v___x_520_, v___y_516_, v___y_517_);
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
v_val_522_ = lean_ctor_get(v_args_x3f_514_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_args_x3f_514_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v_args_x3f_514_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_val_522_);
lean_dec(v_args_x3f_514_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_val_522_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Fmt_fmtSimpLike(v___x_519_, v_cfg_505_, v___x_520_, v___x_520_, v_lbTk_x3f_513_, v___x_527_, v_rbTk_x3f_515_, v___x_520_, v___y_516_, v___y_517_);
return v___x_528_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLiaTactic___boxed(lean_object* v_x_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Fmt_fmtLiaTactic(v_x_546_, v_a_547_, v_a_548_);
lean_dec_ref(v_a_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1(){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_556_ = l_Lean_Fmt_fmtAttribute;
v___x_557_ = ((lean_object*)(l_Lean_Fmt_fmtLiaTactic___closed__1));
v___x_558_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___closed__1));
v___x_559_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLiaTactic___boxed), 3, 0);
v___x_560_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_556_, v___x_557_, v___x_558_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1___boxed(lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1();
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindOrder(lean_object* v_x_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Fmt_fmtGrindOrder___closed__1));
lean_inc(v_x_569_);
v___x_573_ = l_Lean_Syntax_isOfKind(v_x_569_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_x_569_);
v___x_574_ = l_Lean_Fmt_Error_partialFormatter;
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_a_571_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v_cfg_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v_cfg_577_ = l_Lean_Syntax_getArg(v_x_569_, v___x_576_);
v___x_578_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__6));
lean_inc(v_cfg_577_);
v___x_579_ = l_Lean_Syntax_isOfKind(v_cfg_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_cfg_577_);
lean_dec(v_x_569_);
v___x_580_ = l_Lean_Fmt_Error_partialFormatter;
v___x_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_a_571_);
return v___x_581_;
}
else
{
lean_object* v___x_582_; lean_object* v_tk_583_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v_tk_583_ = l_Lean_Syntax_getArg(v_x_569_, v___x_582_);
lean_dec(v_x_569_);
v___x_584_ = l_Lean_Fmt_fmt(v_tk_583_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___x_587_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
v_a_586_ = lean_ctor_get(v___x_584_, 1);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_584_, 2);
v___x_587_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_577_, v_a_586_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v_a_589_; size_t v_sz_590_; size_t v___x_591_; lean_object* v___x_592_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
v_a_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_587_, 2);
v_sz_590_ = lean_array_size(v_a_588_);
v___x_591_ = ((size_t)0ULL);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCutsat_spec__0(v_sz_590_, v___x_591_, v_a_588_, v_a_570_, v_a_589_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_607_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_a_594_ = lean_ctor_get(v___x_592_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_607_ == 0)
{
v___x_596_ = v___x_592_;
v_isShared_597_ = v_isSharedCheck_607_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_607_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_598_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_599_ = lean_array_push(v___x_598_, v_a_585_);
v___x_600_ = l_Array_append___redArg(v___x_599_, v_a_593_);
lean_dec(v_a_593_);
v___x_601_ = 0;
v___x_602_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_602_, 0, v___x_579_);
lean_ctor_set_uint8(v___x_602_, 1, v___x_601_);
lean_ctor_set_uint8(v___x_602_, 2, v___x_601_);
lean_ctor_set_uint8(v___x_602_, 3, v___x_601_);
v___x_603_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_600_, v___x_602_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_603_);
v___x_605_ = v___x_596_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_a_594_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_a_585_);
v_a_608_ = lean_ctor_get(v___x_592_, 0);
v_a_609_ = lean_ctor_get(v___x_592_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_592_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_inc(v_a_608_);
lean_dec(v___x_592_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_608_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_a_585_);
v_a_617_ = lean_ctor_get(v___x_587_, 0);
v_a_618_ = lean_ctor_get(v___x_587_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_587_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_inc(v_a_617_);
lean_dec(v___x_587_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_617_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_dec(v_cfg_577_);
return v___x_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindOrder___boxed(lean_object* v_x_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Fmt_fmtGrindOrder(v_x_626_, v_a_627_, v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1(){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_636_ = l_Lean_Fmt_fmtAttribute;
v___x_637_ = ((lean_object*)(l_Lean_Fmt_fmtGrindOrder___closed__1));
v___x_638_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___closed__1));
v___x_639_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindOrder___boxed), 3, 0);
v___x_640_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_636_, v___x_637_, v___x_638_, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1___boxed(lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1();
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLinarithTactic(lean_object* v_x_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLinarithTactic___closed__1));
lean_inc(v_x_649_);
v___x_653_ = l_Lean_Syntax_isOfKind(v_x_649_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v_x_649_);
v___x_654_ = l_Lean_Fmt_Error_partialFormatter;
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_a_651_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; lean_object* v_cfg_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v_cfg_657_ = l_Lean_Syntax_getArg(v_x_649_, v___x_656_);
v___x_658_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__6));
lean_inc(v_cfg_657_);
v___x_659_ = l_Lean_Syntax_isOfKind(v_cfg_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_cfg_657_);
lean_dec(v_x_649_);
v___x_660_ = l_Lean_Fmt_Error_partialFormatter;
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_a_651_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v_tk_663_; lean_object* v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v_tk_663_ = l_Lean_Syntax_getArg(v_x_649_, v___x_662_);
lean_dec(v_x_649_);
v___x_664_ = l_Lean_Fmt_fmt(v_tk_663_, v_a_650_, v_a_651_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_667_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
v_a_666_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_664_, 2);
v___x_667_ = l_Lean_Fmt_tacticOptConfigItems___redArg(v_cfg_657_, v_a_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v_a_669_; size_t v_sz_670_; size_t v___x_671_; lean_object* v___x_672_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
v_a_669_ = lean_ctor_get(v___x_667_, 1);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_667_, 2);
v_sz_670_ = lean_array_size(v_a_668_);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCutsat_spec__0(v_sz_670_, v___x_671_, v_a_668_, v_a_650_, v_a_669_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_687_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_a_674_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_687_ == 0)
{
v___x_676_ = v___x_672_;
v_isShared_677_ = v_isSharedCheck_687_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_687_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_678_ = lean_mk_empty_array_with_capacity(v___x_656_);
v___x_679_ = lean_array_push(v___x_678_, v_a_665_);
v___x_680_ = l_Array_append___redArg(v___x_679_, v_a_673_);
lean_dec(v_a_673_);
v___x_681_ = 0;
v___x_682_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_682_, 0, v___x_659_);
lean_ctor_set_uint8(v___x_682_, 1, v___x_681_);
lean_ctor_set_uint8(v___x_682_, 2, v___x_681_);
lean_ctor_set_uint8(v___x_682_, 3, v___x_681_);
v___x_683_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_680_, v___x_682_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_683_);
v___x_685_ = v___x_676_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_a_674_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
else
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_a_665_);
v_a_688_ = lean_ctor_get(v___x_672_, 0);
v_a_689_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_672_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_inc(v_a_688_);
lean_dec(v___x_672_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_a_665_);
v_a_697_ = lean_ctor_get(v___x_667_, 0);
v_a_698_ = lean_ctor_get(v___x_667_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_667_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_inc(v_a_697_);
lean_dec(v___x_667_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_697_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_dec(v_cfg_657_);
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLinarithTactic___boxed(lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Fmt_fmtGrindLinarithTactic(v_x_706_, v_a_707_, v_a_708_);
lean_dec_ref(v_a_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1(){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_716_ = l_Lean_Fmt_fmtAttribute;
v___x_717_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLinarithTactic___closed__1));
v___x_718_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___closed__1));
v___x_719_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindLinarithTactic___boxed), 3, 0);
v___x_720_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_716_, v___x_717_, v___x_718_, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1___boxed(lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1();
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrobner(lean_object* v_x_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = ((lean_object*)(l_Lean_Fmt_fmtGrobner___closed__1));
lean_inc(v_x_729_);
v___x_733_ = l_Lean_Syntax_isOfKind(v_x_729_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v_x_729_);
v___x_734_ = l_Lean_Fmt_Error_partialFormatter;
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v_a_731_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; lean_object* v_cfg_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_736_ = lean_unsigned_to_nat(1u);
v_cfg_737_ = l_Lean_Syntax_getArg(v_x_729_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Fmt_fmtGrindTactic___closed__6));
lean_inc(v_cfg_737_);
v___x_739_ = l_Lean_Syntax_isOfKind(v_cfg_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_cfg_737_);
lean_dec(v_x_729_);
v___x_740_ = l_Lean_Fmt_Error_partialFormatter;
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_a_731_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; lean_object* v_tk_743_; lean_object* v_lbTk_x3f_745_; lean_object* v_args_x3f_746_; lean_object* v_rbTk_x3f_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v_tk_743_ = l_Lean_Syntax_getArg(v_x_729_, v___x_742_);
v___x_763_ = lean_unsigned_to_nat(2u);
v___x_764_ = l_Lean_Syntax_getArg(v_x_729_, v___x_763_);
lean_dec(v_x_729_);
v___x_765_ = l_Lean_Syntax_isNone(v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_764_);
v___x_767_ = l_Lean_Syntax_matchesNull(v___x_764_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v___x_764_);
lean_dec(v_tk_743_);
lean_dec(v_cfg_737_);
v___x_768_ = l_Lean_Fmt_Error_partialFormatter;
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v_a_731_);
return v___x_769_;
}
else
{
lean_object* v_lbTk_x3f_770_; lean_object* v___x_771_; lean_object* v_rbTk_x3f_772_; lean_object* v_args_x3f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_lbTk_x3f_770_ = l_Lean_Syntax_getArg(v___x_764_, v___x_742_);
v___x_771_ = l_Lean_Syntax_getArg(v___x_764_, v___x_736_);
v_rbTk_x3f_772_ = l_Lean_Syntax_getArg(v___x_764_, v___x_763_);
lean_dec(v___x_764_);
v_args_x3f_773_ = l_Lean_Syntax_getArgs(v___x_771_);
lean_dec(v___x_771_);
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v_lbTk_x3f_770_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v_args_x3f_773_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_rbTk_x3f_772_);
v_lbTk_x3f_745_ = v___x_774_;
v_args_x3f_746_ = v___x_775_;
v_rbTk_x3f_747_ = v___x_776_;
v___y_748_ = v_a_730_;
v___y_749_ = v_a_731_;
goto v___jp_744_;
}
}
else
{
lean_object* v___x_777_; 
lean_dec(v___x_764_);
v___x_777_ = lean_box(0);
v_lbTk_x3f_745_ = v___x_777_;
v_args_x3f_746_ = v___x_777_;
v_rbTk_x3f_747_ = v___x_777_;
v___y_748_ = v_a_730_;
v___y_749_ = v_a_731_;
goto v___jp_744_;
}
v___jp_744_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_mk_empty_array_with_capacity(v___x_736_);
v___x_751_ = lean_array_push(v___x_750_, v_tk_743_);
v___x_752_ = lean_box(0);
if (lean_obj_tag(v_args_x3f_746_) == 0)
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Fmt_fmtSimpLike(v___x_751_, v_cfg_737_, v___x_752_, v___x_752_, v_lbTk_x3f_745_, v___x_752_, v_rbTk_x3f_747_, v___x_752_, v___y_748_, v___y_749_);
return v___x_753_;
}
else
{
lean_object* v_val_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_val_754_ = lean_ctor_get(v_args_x3f_746_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_args_x3f_746_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v_args_x3f_746_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_val_754_);
lean_dec(v_args_x3f_746_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_val_754_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Fmt_fmtSimpLike(v___x_751_, v_cfg_737_, v___x_752_, v___x_752_, v_lbTk_x3f_745_, v___x_759_, v_rbTk_x3f_747_, v___x_752_, v___y_748_, v___y_749_);
return v___x_760_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrobner___boxed(lean_object* v_x_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Fmt_fmtGrobner(v_x_778_, v_a_779_, v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1(){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_788_ = l_Lean_Fmt_fmtAttribute;
v___x_789_ = ((lean_object*)(l_Lean_Fmt_fmtGrobner___closed__1));
v___x_790_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___closed__1));
v___x_791_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrobner___boxed), 3, 0);
v___x_792_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_788_, v___x_789_, v___x_790_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1___boxed(lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1();
return v_res_794_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTactic___regBuiltin_Lean_Fmt_fmtGrindTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindTraceTactic___regBuiltin_Lean_Fmt_fmtGrindTraceTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtSymTactic___regBuiltin_Lean_Fmt_fmtSymTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtCutsat___regBuiltin_Lean_Fmt_fmtCutsat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtLiaTactic___regBuiltin_Lean_Fmt_fmtLiaTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindOrder___regBuiltin_Lean_Fmt_fmtGrindOrder__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrindLinarithTactic___regBuiltin_Lean_Fmt_fmtGrindLinarithTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Tactics_0__Lean_Fmt_fmtGrobner___regBuiltin_Lean_Fmt_fmtGrobner__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Grind_Tactics(builtin);
}
#ifdef __cplusplus
}
#endif
