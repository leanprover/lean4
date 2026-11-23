// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Grind.Propagator
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Init.Simproc meta import Init.Grind.Propagator import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Fmt_fmtSimprocLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindPropagator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtGrindPropagator___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPropagator___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPropagator___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPropagator___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "command_Grind_propagator___(_):=_"};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagator___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagator___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagator___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__5_value),LEAN_SCALAR_PTR_LITERAL(235, 223, 252, 70, 89, 119, 69, 113)}};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPropagator___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtGrindPropagator___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagator___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagator___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__9_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagator___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__9_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagator___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__9_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__8_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtGrindPropagator___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPropagator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPropagator___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtGrindPropagator"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(33, 208, 199, 74, 226, 10, 141, 205)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "command_Builtin_grind_propagator____:=_"};
static const lean_object* l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 208, 41, 172, 144, 30, 112, 198)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinGrindPropagator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinGrindPropagator___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "fmtBuiltinGrindPropagator"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 140, 254, 152, 87, 168, 125, 134)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "grindPropagatorBuiltinAttr"};
static const lean_object* l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 229, 199, 232, 226, 194, 54, 34)}};
static const lean_object* l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "fmtGrindPropagatorBuiltinAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindPropagator___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 12, 71, 211, 139, 11, 43, 77)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPropagator(lean_object* v_x_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_docComment_x3f_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__6));
lean_inc(v_x_20_);
v___x_55_ = l_Lean_Syntax_isOfKind(v_x_20_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_x_20_);
v___x_56_ = l_Lean_Fmt_Error_partialFormatter;
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v_a_22_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = l_Lean_Syntax_getArg(v_x_20_, v___x_58_);
v___x_60_ = l_Lean_Syntax_isNone(v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_59_);
v___x_62_ = l_Lean_Syntax_matchesNull(v___x_59_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v___x_59_);
lean_dec(v_x_20_);
v___x_63_ = l_Lean_Fmt_Error_partialFormatter;
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v_a_22_);
return v___x_64_;
}
else
{
lean_object* v_docComment_x3f_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_docComment_x3f_65_ = l_Lean_Syntax_getArg(v___x_59_, v___x_58_);
lean_dec(v___x_59_);
v___x_66_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__9));
lean_inc(v_docComment_x3f_65_);
v___x_67_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_docComment_x3f_65_);
lean_dec(v_x_20_);
v___x_68_ = l_Lean_Fmt_Error_partialFormatter;
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_a_22_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; 
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v_docComment_x3f_65_);
v_docComment_x3f_24_ = v___x_70_;
v___y_25_ = v_a_21_;
v___y_26_ = v_a_22_;
goto v___jp_23_;
}
}
}
else
{
lean_object* v___x_71_; 
lean_dec(v___x_59_);
v___x_71_ = lean_box(0);
v_docComment_x3f_24_ = v___x_71_;
v___y_25_ = v_a_21_;
v___y_26_ = v_a_22_;
goto v___jp_23_;
}
}
v___jp_23_:
{
lean_object* v___x_27_; lean_object* v_declId_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = lean_unsigned_to_nat(3u);
v_declId_28_ = l_Lean_Syntax_getArg(v_x_20_, v___x_27_);
v___x_29_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__1));
lean_inc(v_declId_28_);
v___x_30_ = l_Lean_Syntax_isOfKind(v_declId_28_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_declId_28_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
v___x_31_ = l_Lean_Fmt_Error_partialFormatter;
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___y_26_);
return v___x_32_;
}
else
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_33_ = lean_unsigned_to_nat(5u);
v___x_34_ = l_Lean_Syntax_getArg(v_x_20_, v___x_33_);
lean_inc(v___x_34_);
v___x_35_ = l_Lean_Syntax_isOfKind(v___x_34_, v___x_29_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v___x_34_);
lean_dec(v_declId_28_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
v___x_36_ = l_Lean_Fmt_Error_partialFormatter;
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___y_26_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v_grindPropagatorTk_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v_lparenTk_43_; lean_object* v___x_44_; lean_object* v_rparenTk_45_; lean_object* v___x_46_; lean_object* v_colonEqTk_47_; lean_object* v___x_48_; lean_object* v_body_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v_grindPropagatorTk_39_ = l_Lean_Syntax_getArg(v_x_20_, v___x_38_);
v___x_40_ = lean_unsigned_to_nat(2u);
v___x_41_ = l_Lean_Syntax_getArg(v_x_20_, v___x_40_);
v___x_42_ = lean_unsigned_to_nat(4u);
v_lparenTk_43_ = l_Lean_Syntax_getArg(v_x_20_, v___x_42_);
v___x_44_ = lean_unsigned_to_nat(6u);
v_rparenTk_45_ = l_Lean_Syntax_getArg(v_x_20_, v___x_44_);
v___x_46_ = lean_unsigned_to_nat(7u);
v_colonEqTk_47_ = l_Lean_Syntax_getArg(v_x_20_, v___x_46_);
v___x_48_ = lean_unsigned_to_nat(8u);
v_body_49_ = l_Lean_Syntax_getArg(v_x_20_, v___x_48_);
lean_dec(v_x_20_);
v___x_50_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__2));
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_41_);
v___x_52_ = lean_box(0);
v___x_53_ = l_Lean_Fmt_fmtSimprocLike(v_docComment_x3f_24_, v___x_50_, v_grindPropagatorTk_39_, v___x_51_, v___x_52_, v___x_52_, v___x_52_, v_declId_28_, v_lparenTk_43_, v___x_34_, v_rparenTk_45_, v_colonEqTk_47_, v_body_49_, v___y_25_, v___y_26_);
return v___x_53_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPropagator___boxed(lean_object* v_x_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Fmt_fmtGrindPropagator(v_x_72_, v_a_73_, v_a_74_);
lean_dec_ref(v_a_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1(){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = l_Lean_Fmt_fmtAttribute;
v___x_84_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__6));
v___x_85_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___closed__2));
v___x_86_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindPropagator___boxed), 3, 0);
v___x_87_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_83_, v___x_84_, v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1___boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1();
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinGrindPropagator(lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v_docComment_x3f_101_; lean_object* v___y_102_; lean_object* v___y_103_; 
v___x_98_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1));
lean_inc(v_x_95_);
v___x_99_ = l_Lean_Syntax_isOfKind(v_x_95_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_x_95_);
v___x_154_ = l_Lean_Fmt_Error_partialFormatter;
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_97_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = l_Lean_Syntax_getArg(v_x_95_, v___x_156_);
v___x_158_ = l_Lean_Syntax_isNone(v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_157_);
v___x_160_ = l_Lean_Syntax_matchesNull(v___x_157_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v___x_157_);
lean_dec(v_x_95_);
v___x_161_ = l_Lean_Fmt_Error_partialFormatter;
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_97_);
return v___x_162_;
}
else
{
lean_object* v_docComment_x3f_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_docComment_x3f_163_ = l_Lean_Syntax_getArg(v___x_157_, v___x_156_);
lean_dec(v___x_157_);
v___x_164_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__9));
lean_inc(v_docComment_x3f_163_);
v___x_165_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_docComment_x3f_163_);
lean_dec(v_x_95_);
v___x_166_ = l_Lean_Fmt_Error_partialFormatter;
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_97_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v_docComment_x3f_163_);
v_docComment_x3f_101_ = v___x_168_;
v___y_102_ = v_a_96_;
v___y_103_ = v_a_97_;
goto v___jp_100_;
}
}
}
else
{
lean_object* v___x_169_; 
lean_dec(v___x_157_);
v___x_169_ = lean_box(0);
v_docComment_x3f_101_ = v___x_169_;
v___y_102_ = v_a_96_;
v___y_103_ = v_a_97_;
goto v___jp_100_;
}
}
v___jp_100_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_95_, v___x_104_);
v___x_106_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__1));
lean_inc(v___x_105_);
v___x_107_ = l_Lean_Syntax_isOfKind(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v___x_105_);
lean_dec(v_docComment_x3f_101_);
lean_dec(v_x_95_);
v___x_108_ = l_Lean_Fmt_Error_partialFormatter;
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___y_103_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = lean_unsigned_to_nat(4u);
v___x_111_ = l_Lean_Syntax_getArg(v_x_95_, v___x_110_);
lean_inc(v___x_111_);
v___x_112_ = l_Lean_Syntax_isOfKind(v___x_111_, v___x_106_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v___x_111_);
lean_dec(v___x_105_);
lean_dec(v_docComment_x3f_101_);
lean_dec(v_x_95_);
v___x_113_ = l_Lean_Fmt_Error_partialFormatter;
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___y_103_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v_builtinGrindPropagatorTk_116_; lean_object* v___x_117_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v_builtinGrindPropagatorTk_116_ = l_Lean_Syntax_getArg(v_x_95_, v___x_115_);
v___x_117_ = l_Lean_Fmt_fmt(v_builtinGrindPropagatorTk_116_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v_a_119_; lean_object* v___x_120_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
v_a_119_ = lean_ctor_get(v___x_117_, 1);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_117_, 2);
v___x_120_ = l_Lean_Fmt_fmt(v___x_105_, v___y_102_, v_a_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
v_a_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_a_122_);
lean_dec_ref_known(v___x_120_, 2);
v___x_123_ = lean_unsigned_to_nat(3u);
v___x_124_ = l_Lean_Syntax_getArg(v_x_95_, v___x_123_);
v___x_125_ = l_Lean_Fmt_fmt(v___x_124_, v___y_102_, v_a_122_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_126_);
v_a_127_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_a_127_);
lean_dec_ref_known(v___x_125_, 2);
v___x_128_ = l_Lean_Fmt_fmt(v___x_111_, v___y_102_, v_a_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v_a_130_; lean_object* v___x_131_; lean_object* v_colonEqTk_132_; lean_object* v___x_133_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
v_a_130_ = lean_ctor_get(v___x_128_, 1);
lean_inc(v_a_130_);
lean_dec_ref_known(v___x_128_, 2);
v___x_131_ = lean_unsigned_to_nat(5u);
v_colonEqTk_132_ = l_Lean_Syntax_getArg(v_x_95_, v___x_131_);
v___x_133_ = l_Lean_Fmt_fmt(v_colonEqTk_132_, v___y_102_, v_a_130_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v_a_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
v_a_135_ = lean_ctor_get(v___x_133_, 1);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_133_, 2);
v___x_136_ = lean_unsigned_to_nat(6u);
v___x_137_ = l_Lean_Syntax_getArg(v_x_95_, v___x_136_);
lean_dec(v_x_95_);
v___x_138_ = l_Lean_Fmt_fmt(v___x_137_, v___y_102_, v_a_135_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v_a_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
v_a_140_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_a_140_);
lean_dec_ref_known(v___x_138_, 2);
v___x_141_ = 2;
v___x_142_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_126_, v_a_129_, v___x_141_);
v___x_143_ = lean_mk_empty_array_with_capacity(v___x_123_);
v___x_144_ = lean_array_push(v___x_143_, v_a_118_);
v___x_145_ = lean_array_push(v___x_144_, v_a_121_);
v___x_146_ = lean_array_push(v___x_145_, v___x_142_);
v___x_147_ = 0;
v___x_148_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_148_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_148_, 1, v___x_147_);
lean_ctor_set_uint8(v___x_148_, 2, v___x_147_);
lean_ctor_set_uint8(v___x_148_, 3, v___x_147_);
v___x_149_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_146_, v___x_148_);
v___x_150_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_149_, v_a_134_, v_a_139_, v___x_147_);
v___x_151_ = lean_box(0);
v___x_152_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__2));
v___x_153_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_101_, v___x_151_, v___x_152_, v___x_150_, v___y_102_, v_a_140_);
return v___x_153_;
}
else
{
lean_dec(v_a_134_);
lean_dec(v_a_129_);
lean_dec(v_a_126_);
lean_dec(v_a_121_);
lean_dec(v_a_118_);
lean_dec(v_docComment_x3f_101_);
return v___x_138_;
}
}
else
{
lean_dec(v_a_129_);
lean_dec(v_a_126_);
lean_dec(v_a_121_);
lean_dec(v_a_118_);
lean_dec(v_docComment_x3f_101_);
lean_dec(v_x_95_);
return v___x_133_;
}
}
else
{
lean_dec(v_a_126_);
lean_dec(v_a_121_);
lean_dec(v_a_118_);
lean_dec(v_docComment_x3f_101_);
lean_dec(v_x_95_);
return v___x_128_;
}
}
else
{
lean_dec(v_a_121_);
lean_dec(v_a_118_);
lean_dec(v___x_111_);
lean_dec(v_docComment_x3f_101_);
lean_dec(v_x_95_);
return v___x_125_;
}
}
else
{
lean_dec(v_a_118_);
lean_dec(v___x_111_);
lean_dec(v_docComment_x3f_101_);
lean_dec(v_x_95_);
return v___x_120_;
}
}
else
{
lean_dec(v___x_111_);
lean_dec(v___x_105_);
lean_dec(v_docComment_x3f_101_);
lean_dec(v_x_95_);
return v___x_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinGrindPropagator___boxed(lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Fmt_fmtBuiltinGrindPropagator(v_x_170_, v_a_171_, v_a_172_);
lean_dec_ref(v_a_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1(){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_180_ = l_Lean_Fmt_fmtAttribute;
v___x_181_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinGrindPropagator___closed__1));
v___x_182_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___closed__1));
v___x_183_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinGrindPropagator___boxed), 3, 0);
v___x_184_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_180_, v___x_181_, v___x_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1___boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1();
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr(lean_object* v_x_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1));
lean_inc(v_x_192_);
v___x_196_ = l_Lean_Syntax_isOfKind(v_x_192_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_x_192_);
v___x_197_ = l_Lean_Fmt_Error_partialFormatter;
v___x_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_a_194_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_199_ = lean_unsigned_to_nat(2u);
v___x_200_ = l_Lean_Syntax_getArg(v_x_192_, v___x_199_);
v___x_201_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagator___closed__1));
lean_inc(v___x_200_);
v___x_202_ = l_Lean_Syntax_isOfKind(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v___x_200_);
lean_dec(v_x_192_);
v___x_203_ = l_Lean_Fmt_Error_partialFormatter;
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_a_194_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v_builtinGrindPropagatorTk_206_; lean_object* v___x_207_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v_builtinGrindPropagatorTk_206_ = l_Lean_Syntax_getArg(v_x_192_, v___x_205_);
v___x_207_ = l_Lean_Fmt_fmt(v_builtinGrindPropagatorTk_206_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
v_a_209_ = lean_ctor_get(v___x_207_, 1);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_207_, 2);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = l_Lean_Syntax_getArg(v_x_192_, v___x_210_);
lean_dec(v_x_192_);
v___x_212_ = l_Lean_Fmt_fmt(v___x_211_, v_a_193_, v_a_209_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
v_a_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_212_, 2);
v___x_215_ = l_Lean_Fmt_fmt(v___x_200_, v_a_193_, v_a_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_233_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_a_217_ = lean_ctor_get(v___x_215_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_233_ == 0)
{
v___x_219_ = v___x_215_;
v_isShared_220_ = v_isSharedCheck_233_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_233_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_221_ = lean_mk_empty_array_with_capacity(v___x_199_);
lean_inc_ref(v___x_221_);
v___x_222_ = lean_array_push(v___x_221_, v_a_208_);
v___x_223_ = lean_array_push(v___x_222_, v_a_213_);
v___x_224_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_223_);
lean_dec_ref(v___x_223_);
v___x_225_ = lean_array_push(v___x_221_, v___x_224_);
v___x_226_ = lean_array_push(v___x_225_, v_a_216_);
v___x_227_ = 0;
v___x_228_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_228_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_228_, 1, v___x_227_);
lean_ctor_set_uint8(v___x_228_, 2, v___x_227_);
lean_ctor_set_uint8(v___x_228_, 3, v___x_227_);
v___x_229_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_226_, v___x_228_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_229_);
v___x_231_ = v___x_219_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_a_217_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_dec(v_a_213_);
lean_dec(v_a_208_);
return v___x_215_;
}
}
else
{
lean_dec(v_a_208_);
lean_dec(v___x_200_);
return v___x_212_;
}
}
else
{
lean_dec(v___x_200_);
lean_dec(v_x_192_);
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___boxed(lean_object* v_x_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr(v_x_234_, v_a_235_, v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1(){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_244_ = l_Lean_Fmt_fmtAttribute;
v___x_245_ = ((lean_object*)(l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___closed__1));
v___x_246_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___closed__1));
v___x_247_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindPropagatorBuiltinAttr___boxed), 3, 0);
v___x_248_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_244_, v___x_245_, v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1___boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1();
return v_res_250_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagator___regBuiltin_Lean_Fmt_fmtGrindPropagator__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtBuiltinGrindPropagator___regBuiltin_Lean_Fmt_fmtBuiltinGrindPropagator__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Propagator_0__Lean_Fmt_fmtGrindPropagatorBuiltinAttr___regBuiltin_Lean_Fmt_fmtGrindPropagatorBuiltinAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Grind_Propagator(builtin);
}
#ifdef __cplusplus
}
#endif
