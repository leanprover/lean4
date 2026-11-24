// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Grind.Lint
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Grind.Lint import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindLintCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtGrindLintCheck___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGrindLintCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Fmt_fmtGrindLintCheck___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindLintCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grindLintCheck"};
static const lean_object* l_Lean_Fmt_fmtGrindLintCheck___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintCheck___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintCheck___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintCheck___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(62, 113, 74, 13, 3, 158, 65, 234)}};
static const lean_object* l_Lean_Fmt_fmtGrindLintCheck___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__3_value;
static const lean_array_object l_Lean_Fmt_fmtGrindLintCheck___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtGrindLintCheck___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintCheck(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintCheck___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindLintCheck"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(43, 88, 49, 65, 254, 215, 4, 205)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindLintInspect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindLintInspect"};
static const lean_object* l_Lean_Fmt_fmtGrindLintInspect___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintInspect___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintInspect___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintInspect___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLintInspect___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintInspect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLintInspect___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindLintInspect___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 56, 130, 46, 162, 240, 182, 8)}};
static const lean_object* l_Lean_Fmt_fmtGrindLintInspect___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintInspect___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintInspect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintInspect___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGrindLintInspect"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 219, 219, 89, 185, 191, 123, 182)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindLintMute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLintMute"};
static const lean_object* l_Lean_Fmt_fmtGrindLintMute___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintMute___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintMute___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintMute___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLintMute___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintMute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLintMute___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindLintMute___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 30, 63, 16, 186, 128, 138, 7)}};
static const lean_object* l_Lean_Fmt_fmtGrindLintMute___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintMute___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintMute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintMute___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindLintMute"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 90, 171, 12, 46, 163, 30, 170)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindLintSkip___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLintSkip"};
static const lean_object* l_Lean_Fmt_fmtGrindLintSkip___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintSkip___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintSkip___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintSkip___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLintSkip___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindLintSkip___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindLintSkip___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindLintSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 168, 241, 99, 13, 160, 45, 13)}};
static const lean_object* l_Lean_Fmt_fmtGrindLintSkip___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindLintSkip___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintSkip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintSkip___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGrindLintSkip"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 78, 112, 193, 58, 38, 44, 156)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintCheck(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintCheck___closed__3));
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
lean_object* v___x_17_; lean_object* v_grindLintTk_18_; lean_object* v___x_19_; lean_object* v_checkTk_20_; lean_object* v___x_21_; lean_object* v___y_23_; lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; lean_object* v___y_28_; lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v___y_70_; lean_object* v___y_71_; lean_object* v___y_72_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___x_85_; lean_object* v_inTk_x3f_87_; lean_object* v_moduleTk_x3f_88_; lean_object* v_ids_x3f_89_; lean_object* v___y_90_; lean_object* v___y_91_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v_grindLintTk_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
v___x_19_ = lean_unsigned_to_nat(1u);
v_checkTk_20_ = l_Lean_Syntax_getArg(v_x_10_, v___x_19_);
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_85_ = l_Lean_Syntax_getArg(v_x_10_, v___x_21_);
v___x_118_ = lean_unsigned_to_nat(3u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_10_, v___x_118_);
lean_dec(v_x_10_);
v___x_120_ = l_Lean_Syntax_isNone(v___x_119_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
lean_inc(v___x_119_);
v___x_121_ = l_Lean_Syntax_matchesNull(v___x_119_, v___x_118_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v___x_119_);
lean_dec(v___x_85_);
lean_dec(v_checkTk_20_);
lean_dec(v_grindLintTk_18_);
v___x_122_ = l_Lean_Fmt_Error_partialFormatter;
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_a_12_);
return v___x_123_;
}
else
{
lean_object* v_inTk_x3f_124_; lean_object* v_moduleTk_x3f_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_inTk_x3f_124_ = l_Lean_Syntax_getArg(v___x_119_, v___x_17_);
v___x_134_ = l_Lean_Syntax_getArg(v___x_119_, v___x_19_);
v___x_135_ = l_Lean_Syntax_isNone(v___x_134_);
if (v___x_135_ == 0)
{
uint8_t v___x_136_; 
lean_inc(v___x_134_);
v___x_136_ = l_Lean_Syntax_matchesNull(v___x_134_, v___x_19_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v___x_134_);
lean_dec(v_inTk_x3f_124_);
lean_dec(v___x_119_);
lean_dec(v___x_85_);
lean_dec(v_checkTk_20_);
lean_dec(v_grindLintTk_18_);
v___x_137_ = l_Lean_Fmt_Error_partialFormatter;
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_a_12_);
return v___x_138_;
}
else
{
lean_object* v_moduleTk_x3f_139_; lean_object* v___x_140_; 
v_moduleTk_x3f_139_ = l_Lean_Syntax_getArg(v___x_134_, v___x_17_);
lean_dec(v___x_134_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_moduleTk_x3f_139_);
v_moduleTk_x3f_126_ = v___x_140_;
v___y_127_ = v_a_11_;
v___y_128_ = v_a_12_;
goto v___jp_125_;
}
}
else
{
lean_object* v___x_141_; 
lean_dec(v___x_134_);
v___x_141_ = lean_box(0);
v_moduleTk_x3f_126_ = v___x_141_;
v___y_127_ = v_a_11_;
v___y_128_ = v_a_12_;
goto v___jp_125_;
}
v___jp_125_:
{
lean_object* v___x_129_; lean_object* v_ids_x3f_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = l_Lean_Syntax_getArg(v___x_119_, v___x_21_);
lean_dec(v___x_119_);
v_ids_x3f_130_ = l_Lean_Syntax_getArgs(v___x_129_);
lean_dec(v___x_129_);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_inTk_x3f_124_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v_moduleTk_x3f_126_);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v_ids_x3f_130_);
v_inTk_x3f_87_ = v___x_131_;
v_moduleTk_x3f_88_ = v___x_132_;
v_ids_x3f_89_ = v___x_133_;
v___y_90_ = v___y_127_;
v___y_91_ = v___y_128_;
goto v___jp_86_;
}
}
}
else
{
lean_object* v___x_142_; 
lean_dec(v___x_119_);
v___x_142_ = lean_box(0);
v_inTk_x3f_87_ = v___x_142_;
v_moduleTk_x3f_88_ = v___x_142_;
v_ids_x3f_89_ = v___x_142_;
v___y_90_ = v_a_11_;
v___y_91_ = v_a_12_;
goto v___jp_86_;
}
v___jp_22_:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Fmt_fmtArray___redArg(v___y_30_, v___y_24_, v___y_26_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_59_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_59_ == 0)
{
v___x_35_ = v___x_31_;
v_isShared_36_ = v_isSharedCheck_59_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_59_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_37_ = lean_mk_empty_array_with_capacity(v___x_21_);
lean_inc_ref_n(v___x_37_, 2);
v___x_38_ = lean_array_push(v___x_37_, v___y_25_);
v___x_39_ = lean_array_push(v___x_38_, v___y_28_);
v___x_40_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_39_);
lean_dec_ref(v___x_39_);
v___x_41_ = lean_mk_empty_array_with_capacity(v___x_19_);
lean_inc_ref(v___x_41_);
v___x_42_ = lean_array_push(v___x_41_, v___x_40_);
v___x_43_ = l_Array_append___redArg(v___x_42_, v___y_27_);
lean_dec_ref(v___y_27_);
v___x_44_ = 0;
v___x_45_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_45_, 0, v___x_14_);
lean_ctor_set_uint8(v___x_45_, 1, v___x_44_);
lean_ctor_set_uint8(v___x_45_, 2, v___x_44_);
lean_ctor_set_uint8(v___x_45_, 3, v___x_44_);
lean_inc_ref_n(v___x_45_, 2);
v___x_46_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_43_, v___x_45_);
v___x_47_ = lean_array_push(v___x_37_, v___y_23_);
v___x_48_ = lean_array_push(v___x_47_, v___y_29_);
v___x_49_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_48_);
lean_dec_ref(v___x_48_);
v___x_50_ = lean_array_push(v___x_41_, v___x_49_);
v___x_51_ = l_Array_append___redArg(v___x_50_, v_a_32_);
lean_dec(v_a_32_);
v___x_52_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_51_, v___x_45_);
v___x_53_ = lean_array_push(v___x_37_, v___x_46_);
v___x_54_ = lean_array_push(v___x_53_, v___x_52_);
v___x_55_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_54_, v___x_45_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_55_);
v___x_57_ = v___x_35_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_a_33_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_a_60_; lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec_ref(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec_ref(v___y_25_);
lean_dec_ref(v___y_23_);
v_a_60_ = lean_ctor_get(v___x_31_, 0);
v_a_61_ = lean_ctor_get(v___x_31_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_31_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_inc(v_a_60_);
lean_dec(v___x_31_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_60_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
v___jp_69_:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Fmt_fmt_x3f(v___y_77_, v___y_72_, v___y_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
if (lean_obj_tag(v___y_71_) == 0)
{
lean_object* v_a_79_; lean_object* v_a_80_; lean_object* v___x_81_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
v_a_80_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_78_, 2);
v___x_81_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintCheck___closed__4));
v___y_23_ = v___y_70_;
v___y_24_ = v___y_72_;
v___y_25_ = v___y_73_;
v___y_26_ = v_a_80_;
v___y_27_ = v___y_74_;
v___y_28_ = v___y_75_;
v___y_29_ = v_a_79_;
v___y_30_ = v___x_81_;
goto v___jp_22_;
}
else
{
lean_object* v_a_82_; lean_object* v_a_83_; lean_object* v_val_84_; 
v_a_82_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_82_);
v_a_83_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_a_83_);
lean_dec_ref_known(v___x_78_, 2);
v_val_84_ = lean_ctor_get(v___y_71_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v___y_71_, 1);
v___y_23_ = v___y_70_;
v___y_24_ = v___y_72_;
v___y_25_ = v___y_73_;
v___y_26_ = v_a_83_;
v___y_27_ = v___y_74_;
v___y_28_ = v___y_75_;
v___y_29_ = v_a_82_;
v___y_30_ = v_val_84_;
goto v___jp_22_;
}
}
else
{
lean_dec_ref(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v___x_78_;
}
}
v___jp_86_:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Fmt_fmt(v_grindLintTk_18_, v___y_90_, v___y_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v_a_94_; lean_object* v___x_95_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_a_93_);
v_a_94_ = lean_ctor_get(v___x_92_, 1);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_92_, 2);
v___x_95_ = l_Lean_Fmt_fmt(v_checkTk_20_, v___y_90_, v_a_94_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v_a_97_; lean_object* v_cfgItems_98_; lean_object* v___x_99_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
v_a_97_ = lean_ctor_get(v___x_95_, 1);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_95_, 2);
v_cfgItems_98_ = l_Lean_Syntax_getArgs(v___x_85_);
lean_dec(v___x_85_);
v___x_99_ = l_Lean_Fmt_fmtArray___redArg(v_cfgItems_98_, v___y_90_, v_a_97_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v___x_102_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v_a_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_99_, 2);
v___x_102_ = l_Lean_Fmt_fmt_x3f(v_inTk_x3f_87_, v___y_90_, v_a_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
if (lean_obj_tag(v_moduleTk_x3f_88_) == 0)
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_105_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
v_a_104_ = lean_ctor_get(v___x_102_, 1);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_102_, 2);
v___x_105_ = lean_box(0);
v___y_70_ = v_a_103_;
v___y_71_ = v_ids_x3f_89_;
v___y_72_ = v___y_90_;
v___y_73_ = v_a_93_;
v___y_74_ = v_a_100_;
v___y_75_ = v_a_96_;
v___y_76_ = v_a_104_;
v___y_77_ = v___x_105_;
goto v___jp_69_;
}
else
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v_val_108_; 
v_a_106_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_106_);
v_a_107_ = lean_ctor_get(v___x_102_, 1);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_102_, 2);
v_val_108_ = lean_ctor_get(v_moduleTk_x3f_88_, 0);
lean_inc(v_val_108_);
lean_dec_ref_known(v_moduleTk_x3f_88_, 1);
v___y_70_ = v_a_106_;
v___y_71_ = v_ids_x3f_89_;
v___y_72_ = v___y_90_;
v___y_73_ = v_a_93_;
v___y_74_ = v_a_100_;
v___y_75_ = v_a_96_;
v___y_76_ = v_a_107_;
v___y_77_ = v_val_108_;
goto v___jp_69_;
}
}
else
{
lean_dec(v_a_100_);
lean_dec(v_a_96_);
lean_dec(v_a_93_);
lean_dec(v_ids_x3f_89_);
lean_dec(v_moduleTk_x3f_88_);
return v___x_102_;
}
}
else
{
lean_object* v_a_109_; lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec(v_a_96_);
lean_dec(v_a_93_);
lean_dec(v_ids_x3f_89_);
lean_dec(v_moduleTk_x3f_88_);
lean_dec(v_inTk_x3f_87_);
v_a_109_ = lean_ctor_get(v___x_99_, 0);
v_a_110_ = lean_ctor_get(v___x_99_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_99_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_inc(v_a_109_);
lean_dec(v___x_99_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_109_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_dec(v_a_93_);
lean_dec(v_ids_x3f_89_);
lean_dec(v_moduleTk_x3f_88_);
lean_dec(v_inTk_x3f_87_);
lean_dec(v___x_85_);
return v___x_95_;
}
}
else
{
lean_dec(v_ids_x3f_89_);
lean_dec(v_moduleTk_x3f_88_);
lean_dec(v_inTk_x3f_87_);
lean_dec(v___x_85_);
lean_dec(v_checkTk_20_);
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintCheck___boxed(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Fmt_fmtGrindLintCheck(v_x_143_, v_a_144_, v_a_145_);
lean_dec_ref(v_a_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1(){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_154_ = l_Lean_Fmt_fmtAttribute;
v___x_155_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintCheck___closed__3));
v___x_156_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___closed__2));
v___x_157_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindLintCheck___boxed), 3, 0);
v___x_158_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_154_, v___x_155_, v___x_156_, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1___boxed(lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1();
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintInspect(lean_object* v_x_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintInspect___closed__1));
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
lean_object* v___x_173_; lean_object* v_grindLintTk_174_; lean_object* v___x_175_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v_grindLintTk_174_ = l_Lean_Syntax_getArg(v_x_166_, v___x_173_);
v___x_175_ = l_Lean_Fmt_fmt(v_grindLintTk_174_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v_a_177_; lean_object* v___x_178_; lean_object* v_inspectTk_179_; lean_object* v___x_180_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
v_a_177_ = lean_ctor_get(v___x_175_, 1);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_175_, 2);
v___x_178_ = lean_unsigned_to_nat(1u);
v_inspectTk_179_ = l_Lean_Syntax_getArg(v_x_166_, v___x_178_);
v___x_180_ = l_Lean_Fmt_fmt(v_inspectTk_179_, v_a_167_, v_a_177_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v_a_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_cfgItems_185_; lean_object* v___x_186_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
v_a_182_ = lean_ctor_get(v___x_180_, 1);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_180_, 2);
v___x_183_ = lean_unsigned_to_nat(2u);
v___x_184_ = l_Lean_Syntax_getArg(v_x_166_, v___x_183_);
v_cfgItems_185_ = l_Lean_Syntax_getArgs(v___x_184_);
lean_dec(v___x_184_);
v___x_186_ = l_Lean_Fmt_fmtArray___redArg(v_cfgItems_185_, v_a_167_, v_a_182_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v_a_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_ids_191_; lean_object* v___x_192_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
v_a_188_ = lean_ctor_get(v___x_186_, 1);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_186_, 2);
v___x_189_ = lean_unsigned_to_nat(3u);
v___x_190_ = l_Lean_Syntax_getArg(v_x_166_, v___x_189_);
lean_dec(v_x_166_);
v_ids_191_ = l_Lean_Syntax_getArgs(v___x_190_);
lean_dec(v___x_190_);
v___x_192_ = l_Lean_Fmt_fmtArray___redArg(v_ids_191_, v_a_167_, v_a_188_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_214_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_a_194_ = lean_ctor_get(v___x_192_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_214_ == 0)
{
v___x_196_ = v___x_192_;
v_isShared_197_ = v_isSharedCheck_214_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_214_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_198_ = lean_mk_empty_array_with_capacity(v___x_183_);
v___x_199_ = lean_array_push(v___x_198_, v_a_176_);
v___x_200_ = lean_array_push(v___x_199_, v_a_181_);
v___x_201_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_200_);
lean_dec_ref(v___x_200_);
v___x_202_ = lean_mk_empty_array_with_capacity(v___x_178_);
lean_inc_ref(v___x_202_);
v___x_203_ = lean_array_push(v___x_202_, v___x_201_);
v___x_204_ = l_Array_append___redArg(v___x_203_, v_a_187_);
lean_dec(v_a_187_);
v___x_205_ = 0;
v___x_206_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_206_, 0, v___x_170_);
lean_ctor_set_uint8(v___x_206_, 1, v___x_205_);
lean_ctor_set_uint8(v___x_206_, 2, v___x_205_);
lean_ctor_set_uint8(v___x_206_, 3, v___x_205_);
lean_inc_ref(v___x_206_);
v___x_207_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_204_, v___x_206_);
v___x_208_ = lean_array_push(v___x_202_, v___x_207_);
v___x_209_ = l_Array_append___redArg(v___x_208_, v_a_193_);
lean_dec(v_a_193_);
v___x_210_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_209_, v___x_206_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_210_);
v___x_212_ = v___x_196_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_a_194_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_object* v_a_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec(v_a_187_);
lean_dec(v_a_181_);
lean_dec(v_a_176_);
v_a_215_ = lean_ctor_get(v___x_192_, 0);
v_a_216_ = lean_ctor_get(v___x_192_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_192_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_inc(v_a_215_);
lean_dec(v___x_192_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_215_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_a_224_; lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_a_181_);
lean_dec(v_a_176_);
lean_dec(v_x_166_);
v_a_224_ = lean_ctor_get(v___x_186_, 0);
v_a_225_ = lean_ctor_get(v___x_186_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_186_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_inc(v_a_224_);
lean_dec(v___x_186_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_224_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_dec(v_a_176_);
lean_dec(v_x_166_);
return v___x_180_;
}
}
else
{
lean_dec(v_x_166_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintInspect___boxed(lean_object* v_x_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Fmt_fmtGrindLintInspect(v_x_233_, v_a_234_, v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1(){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = l_Lean_Fmt_fmtAttribute;
v___x_244_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintInspect___closed__1));
v___x_245_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___closed__1));
v___x_246_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindLintInspect___boxed), 3, 0);
v___x_247_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_243_, v___x_244_, v___x_245_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1___boxed(lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1();
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintMute(lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintMute___closed__1));
lean_inc(v_x_255_);
v___x_259_ = l_Lean_Syntax_isOfKind(v_x_255_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_x_255_);
v___x_260_ = l_Lean_Fmt_Error_partialFormatter;
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v_grindLintTk_263_; lean_object* v___x_264_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v_grindLintTk_263_ = l_Lean_Syntax_getArg(v_x_255_, v___x_262_);
v___x_264_ = l_Lean_Fmt_fmt(v_grindLintTk_263_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v_a_266_; lean_object* v___x_267_; lean_object* v_muteTk_268_; lean_object* v___x_269_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
v_a_266_ = lean_ctor_get(v___x_264_, 1);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_264_, 2);
v___x_267_ = lean_unsigned_to_nat(1u);
v_muteTk_268_ = l_Lean_Syntax_getArg(v_x_255_, v___x_267_);
v___x_269_ = l_Lean_Fmt_fmt(v_muteTk_268_, v_a_256_, v_a_266_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_ids_274_; lean_object* v___x_275_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
v_a_271_ = lean_ctor_get(v___x_269_, 1);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_269_, 2);
v___x_272_ = lean_unsigned_to_nat(2u);
v___x_273_ = l_Lean_Syntax_getArg(v_x_255_, v___x_272_);
lean_dec(v_x_255_);
v_ids_274_ = l_Lean_Syntax_getArgs(v___x_273_);
lean_dec(v___x_273_);
v___x_275_ = l_Lean_Fmt_fmtArray___redArg(v_ids_274_, v_a_256_, v_a_271_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_294_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_a_277_ = lean_ctor_get(v___x_275_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_294_ == 0)
{
v___x_279_ = v___x_275_;
v_isShared_280_ = v_isSharedCheck_294_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_294_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_272_);
v___x_282_ = lean_array_push(v___x_281_, v_a_265_);
v___x_283_ = lean_array_push(v___x_282_, v_a_270_);
v___x_284_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_283_);
lean_dec_ref(v___x_283_);
v___x_285_ = lean_mk_empty_array_with_capacity(v___x_267_);
v___x_286_ = lean_array_push(v___x_285_, v___x_284_);
v___x_287_ = l_Array_append___redArg(v___x_286_, v_a_276_);
lean_dec(v_a_276_);
v___x_288_ = 0;
v___x_289_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_289_, 0, v___x_259_);
lean_ctor_set_uint8(v___x_289_, 1, v___x_288_);
lean_ctor_set_uint8(v___x_289_, 2, v___x_288_);
lean_ctor_set_uint8(v___x_289_, 3, v___x_288_);
v___x_290_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_287_, v___x_289_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_290_);
v___x_292_ = v___x_279_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_a_277_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_a_295_; lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v_a_270_);
lean_dec(v_a_265_);
v_a_295_ = lean_ctor_get(v___x_275_, 0);
v_a_296_ = lean_ctor_get(v___x_275_, 1);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_275_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_inc(v_a_295_);
lean_dec(v___x_275_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_295_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_dec(v_a_265_);
lean_dec(v_x_255_);
return v___x_269_;
}
}
else
{
lean_dec(v_x_255_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintMute___boxed(lean_object* v_x_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Fmt_fmtGrindLintMute(v_x_304_, v_a_305_, v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1(){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_314_ = l_Lean_Fmt_fmtAttribute;
v___x_315_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintMute___closed__1));
v___x_316_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___closed__1));
v___x_317_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindLintMute___boxed), 3, 0);
v___x_318_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_314_, v___x_315_, v___x_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1___boxed(lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1();
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintSkip(lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintSkip___closed__1));
lean_inc(v_x_326_);
v___x_330_ = l_Lean_Syntax_isOfKind(v_x_326_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_x_326_);
v___x_331_ = l_Lean_Fmt_Error_partialFormatter;
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_a_328_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v_grindLintTk_334_; lean_object* v___x_335_; lean_object* v_skipTk_336_; lean_object* v_suffixTk_x3f_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v_grindLintTk_334_ = l_Lean_Syntax_getArg(v_x_326_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(1u);
v_skipTk_336_ = l_Lean_Syntax_getArg(v_x_326_, v___x_335_);
v___x_383_ = lean_unsigned_to_nat(2u);
v___x_384_ = l_Lean_Syntax_getArg(v_x_326_, v___x_383_);
v___x_385_ = l_Lean_Syntax_isNone(v___x_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; 
lean_inc(v___x_384_);
v___x_386_ = l_Lean_Syntax_matchesNull(v___x_384_, v___x_335_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v___x_384_);
lean_dec(v_skipTk_336_);
lean_dec(v_grindLintTk_334_);
lean_dec(v_x_326_);
v___x_387_ = l_Lean_Fmt_Error_partialFormatter;
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_a_328_);
return v___x_388_;
}
else
{
lean_object* v_suffixTk_x3f_389_; lean_object* v___x_390_; 
v_suffixTk_x3f_389_ = l_Lean_Syntax_getArg(v___x_384_, v___x_333_);
lean_dec(v___x_384_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v_suffixTk_x3f_389_);
v_suffixTk_x3f_338_ = v___x_390_;
v___y_339_ = v_a_327_;
v___y_340_ = v_a_328_;
goto v___jp_337_;
}
}
else
{
lean_object* v___x_391_; 
lean_dec(v___x_384_);
v___x_391_ = lean_box(0);
v_suffixTk_x3f_338_ = v___x_391_;
v___y_339_ = v_a_327_;
v___y_340_ = v_a_328_;
goto v___jp_337_;
}
v___jp_337_:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Fmt_fmt(v_grindLintTk_334_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v_a_343_; lean_object* v___x_344_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
v_a_343_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_341_, 2);
v___x_344_ = l_Lean_Fmt_fmt(v_skipTk_336_, v___y_339_, v_a_343_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v_a_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
v_a_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_344_, 2);
v___x_347_ = l_Lean_Fmt_fmt_x3f(v_suffixTk_x3f_338_, v___y_339_, v_a_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_ids_352_; lean_object* v___x_353_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
v_a_349_ = lean_ctor_get(v___x_347_, 1);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_347_, 2);
v___x_350_ = lean_unsigned_to_nat(3u);
v___x_351_ = l_Lean_Syntax_getArg(v_x_326_, v___x_350_);
lean_dec(v_x_326_);
v_ids_352_ = l_Lean_Syntax_getArgs(v___x_351_);
lean_dec(v___x_351_);
v___x_353_ = l_Lean_Fmt_fmtArray___redArg(v_ids_352_, v___y_339_, v_a_349_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_373_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_a_355_ = lean_ctor_get(v___x_353_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_373_ == 0)
{
v___x_357_ = v___x_353_;
v_isShared_358_ = v_isSharedCheck_373_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_373_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_359_ = lean_mk_empty_array_with_capacity(v___x_350_);
v___x_360_ = lean_array_push(v___x_359_, v_a_342_);
v___x_361_ = lean_array_push(v___x_360_, v_a_345_);
v___x_362_ = lean_array_push(v___x_361_, v_a_348_);
v___x_363_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_362_);
lean_dec_ref(v___x_362_);
v___x_364_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_365_ = lean_array_push(v___x_364_, v___x_363_);
v___x_366_ = l_Array_append___redArg(v___x_365_, v_a_354_);
lean_dec(v_a_354_);
v___x_367_ = 0;
v___x_368_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_368_, 0, v___x_330_);
lean_ctor_set_uint8(v___x_368_, 1, v___x_367_);
lean_ctor_set_uint8(v___x_368_, 2, v___x_367_);
lean_ctor_set_uint8(v___x_368_, 3, v___x_367_);
v___x_369_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_366_, v___x_368_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_369_);
v___x_371_ = v___x_357_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_a_355_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_a_348_);
lean_dec(v_a_345_);
lean_dec(v_a_342_);
v_a_374_ = lean_ctor_get(v___x_353_, 0);
v_a_375_ = lean_ctor_get(v___x_353_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_353_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_inc(v_a_374_);
lean_dec(v___x_353_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_374_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_dec(v_a_345_);
lean_dec(v_a_342_);
lean_dec(v_x_326_);
return v___x_347_;
}
}
else
{
lean_dec(v_a_342_);
lean_dec(v_suffixTk_x3f_338_);
lean_dec(v_x_326_);
return v___x_344_;
}
}
else
{
lean_dec(v_suffixTk_x3f_338_);
lean_dec(v_skipTk_336_);
lean_dec(v_x_326_);
return v___x_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindLintSkip___boxed(lean_object* v_x_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Fmt_fmtGrindLintSkip(v_x_392_, v_a_393_, v_a_394_);
lean_dec_ref(v_a_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1(){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_402_ = l_Lean_Fmt_fmtAttribute;
v___x_403_ = ((lean_object*)(l_Lean_Fmt_fmtGrindLintSkip___closed__1));
v___x_404_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___closed__1));
v___x_405_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindLintSkip___boxed), 3, 0);
v___x_406_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_402_, v___x_403_, v___x_404_, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1___boxed(lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1();
return v_res_408_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Lint(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintCheck___regBuiltin_Lean_Fmt_fmtGrindLintCheck__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintInspect___regBuiltin_Lean_Fmt_fmtGrindLintInspect__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintMute___regBuiltin_Lean_Fmt_fmtGrindLintMute__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Lint_0__Lean_Fmt_fmtGrindLintSkip___regBuiltin_Lean_Fmt_fmtGrindLintSkip__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Lint(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Lint(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Grind_Lint(builtin);
}
#ifdef __cplusplus
}
#endif
