// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.TacticsExtra
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.TacticsExtra import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtRwLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtIterate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtIterate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtIterate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtIterate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticIterate____"};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIterate___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIterate___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIterate___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 47, 56, 55, 14, 165, 150, 141)}};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtIterate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIterate___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIterate___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIterate___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtIterate___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtIterate___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtIterate___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtIterate___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIterate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIterate___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtIterate"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 171, 117, 100, 130, 108, 111, 191)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRwModCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticRw_mod_cast___"};
static const lean_object* l_Lean_Fmt_fmtRwModCast___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 49, 244, 227, 69, 23, 138, 35)}};
static const lean_object* l_Lean_Fmt_fmtRwModCast___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRwModCast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Fmt_fmtRwModCast___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Fmt_fmtRwModCast___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtRwModCast___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l_Lean_Fmt_fmtRwModCast___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__4_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l_Lean_Fmt_fmtRwModCast___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtRwModCast___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Fmt_fmtRwModCast___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__7_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__7_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRwModCast___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__7_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__6_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Fmt_fmtRwModCast___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtRwModCast___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRwModCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRwModCast___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtRwModCast"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 201, 7, 78, 200, 207, 35, 54)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExactModCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticExact_mod_cast_"};
static const lean_object* l_Lean_Fmt_fmtExactModCast___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExactModCast___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExactModCast___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExactModCast___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExactModCast___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtExactModCast___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExactModCast___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtExactModCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExactModCast___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtExactModCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 115, 207, 153, 244, 77, 215, 161)}};
static const lean_object* l_Lean_Fmt_fmtExactModCast___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExactModCast___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExactModCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExactModCast___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtExactModCast"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 222, 206, 80, 153, 182, 7, 224)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtApplyModCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticApply_mod_cast_"};
static const lean_object* l_Lean_Fmt_fmtApplyModCast___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtApplyModCast___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtApplyModCast___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtApplyModCast___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtApplyModCast___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtApplyModCast___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtApplyModCast___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtApplyModCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtApplyModCast___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtApplyModCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 137, 51, 123, 254, 235, 255, 128)}};
static const lean_object* l_Lean_Fmt_fmtApplyModCast___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtApplyModCast___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtApplyModCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtApplyModCast___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtApplyModCast"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIterate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 56, 78, 222, 7, 80, 166, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIterate(lean_object* v_x_19_, lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; uint8_t v___x_23_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; lean_object* v___y_28_; lean_object* v___y_29_; lean_object* v___y_30_; 
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtIterate___closed__4));
lean_inc(v_x_19_);
v___x_23_ = l_Lean_Syntax_isOfKind(v_x_19_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_x_19_);
v___x_52_ = l_Lean_Fmt_Error_partialFormatter;
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v_a_21_);
return v___x_53_;
}
else
{
lean_object* v___x_54_; lean_object* v_iterateTk_55_; lean_object* v_n_x3f_57_; lean_object* v___y_58_; lean_object* v___y_59_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v_iterateTk_55_ = l_Lean_Syntax_getArg(v_x_19_, v___x_54_);
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_19_, v___x_80_);
v___x_82_ = l_Lean_Syntax_isNone(v___x_81_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; 
lean_inc(v___x_81_);
v___x_83_ = l_Lean_Syntax_matchesNull(v___x_81_, v___x_80_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v___x_81_);
lean_dec(v_iterateTk_55_);
lean_dec(v_x_19_);
v___x_84_ = l_Lean_Fmt_Error_partialFormatter;
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v_a_21_);
return v___x_85_;
}
else
{
lean_object* v_n_x3f_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v_n_x3f_86_ = l_Lean_Syntax_getArg(v___x_81_, v___x_54_);
lean_dec(v___x_81_);
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtIterate___closed__8));
lean_inc(v_n_x3f_86_);
v___x_88_ = l_Lean_Syntax_isOfKind(v_n_x3f_86_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_n_x3f_86_);
lean_dec(v_iterateTk_55_);
lean_dec(v_x_19_);
v___x_89_ = l_Lean_Fmt_Error_partialFormatter;
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_a_21_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_n_x3f_86_);
v_n_x3f_57_ = v___x_91_;
v___y_58_ = v_a_20_;
v___y_59_ = v_a_21_;
goto v___jp_56_;
}
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v___x_81_);
v___x_92_ = lean_box(0);
v_n_x3f_57_ = v___x_92_;
v___y_58_ = v_a_20_;
v___y_59_ = v_a_21_;
goto v___jp_56_;
}
v___jp_56_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_60_ = lean_unsigned_to_nat(2u);
v___x_61_ = l_Lean_Syntax_getArg(v_x_19_, v___x_60_);
lean_dec(v_x_19_);
v___x_62_ = ((lean_object*)(l_Lean_Fmt_fmtIterate___closed__6));
lean_inc(v___x_61_);
v___x_63_ = l_Lean_Syntax_isOfKind(v___x_61_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v___x_61_);
lean_dec(v_n_x3f_57_);
lean_dec(v_iterateTk_55_);
v___x_64_ = l_Lean_Fmt_Error_partialFormatter;
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___y_59_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Fmt_fmt(v_iterateTk_55_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_66_) == 0)
{
if (lean_obj_tag(v_n_x3f_57_) == 0)
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_69_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
v_a_68_ = lean_ctor_get(v___x_66_, 1);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_66_, 2);
v___x_69_ = lean_box(0);
v___y_25_ = v_a_68_;
v___y_26_ = v___x_60_;
v___y_27_ = v_a_67_;
v___y_28_ = v___x_61_;
v___y_29_ = v___y_58_;
v___y_30_ = v___x_69_;
goto v___jp_24_;
}
else
{
lean_object* v_a_70_; lean_object* v_a_71_; lean_object* v_val_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
v_a_70_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_70_);
v_a_71_ = lean_ctor_get(v___x_66_, 1);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_66_, 2);
v_val_72_ = lean_ctor_get(v_n_x3f_57_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_n_x3f_57_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v_n_x3f_57_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_val_72_);
lean_dec(v_n_x3f_57_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_val_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
v___y_25_ = v_a_71_;
v___y_26_ = v___x_60_;
v___y_27_ = v_a_70_;
v___y_28_ = v___x_61_;
v___y_29_ = v___y_58_;
v___y_30_ = v___x_77_;
goto v___jp_24_;
}
}
}
}
else
{
lean_dec(v___x_61_);
lean_dec(v_n_x3f_57_);
return v___x_66_;
}
}
}
}
v___jp_24_:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Fmt_fmt_x3f(v___y_30_, v___y_29_, v___y_25_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v_a_33_; uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_a_32_);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
lean_inc(v_a_33_);
lean_dec_ref_known(v___x_31_, 2);
v___x_34_ = 0;
v___x_35_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_35_, 0, v___x_23_);
lean_ctor_set_uint8(v___x_35_, 1, v___x_34_);
lean_ctor_set_uint8(v___x_35_, 2, v___x_34_);
lean_ctor_set_uint8(v___x_35_, 3, v___x_34_);
v___x_36_ = l_Lean_Fmt_fmt(v___y_28_, v___y_29_, v_a_33_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_51_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_a_38_ = lean_ctor_get(v___x_36_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_51_ == 0)
{
v___x_40_ = v___x_36_;
v_isShared_41_ = v_isSharedCheck_51_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_51_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_42_ = lean_mk_empty_array_with_capacity(v___y_26_);
v___x_43_ = lean_array_push(v___x_42_, v___y_27_);
v___x_44_ = lean_array_push(v___x_43_, v_a_32_);
v___x_45_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_44_, v___x_35_);
v___x_46_ = 1;
v___x_47_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v___x_45_, v_a_37_, v___x_46_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v___x_47_);
v___x_49_ = v___x_40_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_a_38_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
else
{
lean_dec_ref_known(v___x_35_, 0);
lean_dec(v_a_32_);
lean_dec_ref(v___y_27_);
return v___x_36_;
}
}
else
{
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIterate___boxed(lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Fmt_fmtIterate(v_x_93_, v_a_94_, v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1(){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_104_ = l_Lean_Fmt_fmtAttribute;
v___x_105_ = ((lean_object*)(l_Lean_Fmt_fmtIterate___closed__4));
v___x_106_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___closed__2));
v___x_107_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtIterate___boxed), 3, 0);
v___x_108_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_104_, v___x_105_, v___x_106_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1___boxed(lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1();
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRwModCast(lean_object* v_x_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Fmt_fmtRwModCast___closed__1));
lean_inc(v_x_135_);
v___x_139_ = l_Lean_Syntax_isOfKind(v_x_135_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_x_135_);
v___x_140_ = l_Lean_Fmt_Error_partialFormatter;
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_a_137_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v_cfg_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v_cfg_143_ = l_Lean_Syntax_getArg(v_x_135_, v___x_142_);
v___x_144_ = ((lean_object*)(l_Lean_Fmt_fmtRwModCast___closed__3));
lean_inc(v_cfg_143_);
v___x_145_ = l_Lean_Syntax_isOfKind(v_cfg_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_cfg_143_);
lean_dec(v_x_135_);
v___x_146_ = l_Lean_Fmt_Error_partialFormatter;
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_a_137_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_148_ = lean_unsigned_to_nat(2u);
v___x_149_ = l_Lean_Syntax_getArg(v_x_135_, v___x_148_);
v___x_150_ = ((lean_object*)(l_Lean_Fmt_fmtRwModCast___closed__5));
lean_inc(v___x_149_);
v___x_151_ = l_Lean_Syntax_isOfKind(v___x_149_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v___x_149_);
lean_dec(v_cfg_143_);
lean_dec(v_x_135_);
v___x_152_ = l_Lean_Fmt_Error_partialFormatter;
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_a_137_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v_rwTk_155_; lean_object* v_loc_x3f_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v_rwTk_155_ = l_Lean_Syntax_getArg(v_x_135_, v___x_154_);
v___x_162_ = lean_unsigned_to_nat(3u);
v___x_163_ = l_Lean_Syntax_getArg(v_x_135_, v___x_162_);
lean_dec(v_x_135_);
v___x_164_ = l_Lean_Syntax_isNone(v___x_163_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; 
lean_inc(v___x_163_);
v___x_165_ = l_Lean_Syntax_matchesNull(v___x_163_, v___x_142_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v___x_163_);
lean_dec(v_rwTk_155_);
lean_dec(v___x_149_);
lean_dec(v_cfg_143_);
v___x_166_ = l_Lean_Fmt_Error_partialFormatter;
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_137_);
return v___x_167_;
}
else
{
lean_object* v_loc_x3f_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_loc_x3f_168_ = l_Lean_Syntax_getArg(v___x_163_, v___x_154_);
lean_dec(v___x_163_);
v___x_169_ = ((lean_object*)(l_Lean_Fmt_fmtRwModCast___closed__7));
lean_inc(v_loc_x3f_168_);
v___x_170_ = l_Lean_Syntax_isOfKind(v_loc_x3f_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_loc_x3f_168_);
lean_dec(v_rwTk_155_);
lean_dec(v___x_149_);
lean_dec(v_cfg_143_);
v___x_171_ = l_Lean_Fmt_Error_partialFormatter;
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_a_137_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v_loc_x3f_168_);
v_loc_x3f_157_ = v___x_173_;
v___y_158_ = v_a_136_;
v___y_159_ = v_a_137_;
goto v___jp_156_;
}
}
}
else
{
lean_object* v___x_174_; 
lean_dec(v___x_163_);
v___x_174_ = lean_box(0);
v_loc_x3f_157_ = v___x_174_;
v___y_158_ = v_a_136_;
v___y_159_ = v_a_137_;
goto v___jp_156_;
}
v___jp_156_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v_cfg_143_);
v___x_161_ = l_Lean_Fmt_fmtRwLike(v_rwTk_155_, v___x_160_, v___x_149_, v_loc_x3f_157_, v___y_158_, v___y_159_);
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRwModCast___boxed(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Fmt_fmtRwModCast(v_x_175_, v_a_176_, v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1(){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_185_ = l_Lean_Fmt_fmtAttribute;
v___x_186_ = ((lean_object*)(l_Lean_Fmt_fmtRwModCast___closed__1));
v___x_187_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___closed__1));
v___x_188_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRwModCast___boxed), 3, 0);
v___x_189_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_185_, v___x_186_, v___x_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1___boxed(lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1();
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExactModCast(lean_object* v_x_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Fmt_fmtExactModCast___closed__1));
lean_inc(v_x_198_);
v___x_202_ = l_Lean_Syntax_isOfKind(v_x_198_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_x_198_);
v___x_203_ = l_Lean_Fmt_Error_partialFormatter;
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_a_200_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v_exactTk_206_; lean_object* v___x_207_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v_exactTk_206_ = l_Lean_Syntax_getArg(v_x_198_, v___x_205_);
v___x_207_ = l_Lean_Fmt_fmt(v_exactTk_206_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
v_a_209_ = lean_ctor_get(v___x_207_, 1);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_207_, 2);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = l_Lean_Syntax_getArg(v_x_198_, v___x_210_);
lean_dec(v_x_198_);
v___x_212_ = l_Lean_Fmt_fmt(v___x_211_, v_a_199_, v_a_209_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_228_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_a_214_ = lean_ctor_get(v___x_212_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_228_ == 0)
{
v___x_216_ = v___x_212_;
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_mk_empty_array_with_capacity(v___x_218_);
v___x_220_ = lean_array_push(v___x_219_, v_a_208_);
v___x_221_ = lean_array_push(v___x_220_, v_a_213_);
v___x_222_ = 0;
v___x_223_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_223_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_223_, 1, v___x_222_);
lean_ctor_set_uint8(v___x_223_, 2, v___x_222_);
lean_ctor_set_uint8(v___x_223_, 3, v___x_222_);
v___x_224_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_221_, v___x_223_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_224_);
v___x_226_ = v___x_216_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_a_214_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_dec(v_a_208_);
return v___x_212_;
}
}
else
{
lean_dec(v_x_198_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExactModCast___boxed(lean_object* v_x_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Fmt_fmtExactModCast(v_x_229_, v_a_230_, v_a_231_);
lean_dec_ref(v_a_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1(){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_239_ = l_Lean_Fmt_fmtAttribute;
v___x_240_ = ((lean_object*)(l_Lean_Fmt_fmtExactModCast___closed__1));
v___x_241_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___closed__1));
v___x_242_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExactModCast___boxed), 3, 0);
v___x_243_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_239_, v___x_240_, v___x_241_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1___boxed(lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1();
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtApplyModCast(lean_object* v_x_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_Fmt_fmtApplyModCast___closed__1));
lean_inc(v_x_252_);
v___x_256_ = l_Lean_Syntax_isOfKind(v_x_252_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_x_252_);
v___x_257_ = l_Lean_Fmt_Error_partialFormatter;
v___x_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_a_254_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; lean_object* v_applyTk_260_; lean_object* v___x_261_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v_applyTk_260_ = l_Lean_Syntax_getArg(v_x_252_, v___x_259_);
v___x_261_ = l_Lean_Fmt_fmt(v_applyTk_260_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v_a_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
v_a_263_ = lean_ctor_get(v___x_261_, 1);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_261_, 2);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = l_Lean_Syntax_getArg(v_x_252_, v___x_264_);
lean_dec(v_x_252_);
v___x_266_ = l_Lean_Fmt_fmt(v___x_265_, v_a_253_, v_a_263_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_282_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_a_268_ = lean_ctor_get(v___x_266_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_282_ == 0)
{
v___x_270_ = v___x_266_;
v_isShared_271_ = v_isSharedCheck_282_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_282_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_272_ = lean_unsigned_to_nat(2u);
v___x_273_ = lean_mk_empty_array_with_capacity(v___x_272_);
v___x_274_ = lean_array_push(v___x_273_, v_a_262_);
v___x_275_ = lean_array_push(v___x_274_, v_a_267_);
v___x_276_ = 0;
v___x_277_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_277_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_277_, 1, v___x_276_);
lean_ctor_set_uint8(v___x_277_, 2, v___x_276_);
lean_ctor_set_uint8(v___x_277_, 3, v___x_276_);
v___x_278_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_275_, v___x_277_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_278_);
v___x_280_ = v___x_270_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_a_268_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_dec(v_a_262_);
return v___x_266_;
}
}
else
{
lean_dec(v_x_252_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtApplyModCast___boxed(lean_object* v_x_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Fmt_fmtApplyModCast(v_x_283_, v_a_284_, v_a_285_);
lean_dec_ref(v_a_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1(){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_293_ = l_Lean_Fmt_fmtAttribute;
v___x_294_ = ((lean_object*)(l_Lean_Fmt_fmtApplyModCast___closed__1));
v___x_295_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___closed__1));
v___x_296_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtApplyModCast___boxed), 3, 0);
v___x_297_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_293_, v___x_294_, v___x_295_, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1___boxed(lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1();
return v_res_299_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_TacticsExtra(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtIterate___regBuiltin_Lean_Fmt_fmtIterate__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtRwModCast___regBuiltin_Lean_Fmt_fmtRwModCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtExactModCast___regBuiltin_Lean_Fmt_fmtExactModCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_TacticsExtra_0__Lean_Fmt_fmtApplyModCast___regBuiltin_Lean_Fmt_fmtApplyModCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_TacticsExtra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_TacticsExtra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_TacticsExtra(builtin);
}
#ifdef __cplusplus
}
#endif
