// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Simproc
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Simproc meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimprocLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtSimprocLike___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimprocLike___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimprocLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtSimprocLike___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimprocLike___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimprocLike___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtSimprocLike___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimprocLike___closed__2_value;
static const lean_array_object l_Lean_Fmt_fmtSimprocLike___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtSimprocLike___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSimprocLike___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocPatternLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocPatternLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocAttrLike(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocAttrLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSimproc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtSimproc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "command__Simproc__[_]_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 10, 201, 188, 148, 134, 66, 9)}};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtSimproc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtSimproc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__7_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtSimproc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__9_value;
static const lean_string_object l_Lean_Fmt_fmtSimproc___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__11_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__11_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__9_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimproc___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__11_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__10_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtSimproc___closed__11 = (const lean_object*)&l_Lean_Fmt_fmtSimproc___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimproc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtSimproc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 169, 123, 48, 92, 219, 86, 181)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "command__Dsimproc__[_]_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtDSimproc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDSimproc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDSimproc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDSimproc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDSimproc___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDSimproc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDSimproc___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDSimproc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 16, 232, 139, 82, 11, 60, 99)}};
static const lean_object* l_Lean_Fmt_fmtDSimproc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDSimproc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimproc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDSimproc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 149, 63, 38, 27, 85, 230, 144)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___boxed(lean_object*);
static const lean_array_object l_Lean_Fmt_fmtSimprocDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtSimprocDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimprocDecl___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSimprocDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "command_Simproc_decl_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtSimprocDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimprocDecl___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimprocDecl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimprocDecl___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimprocDecl___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimprocDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimprocDecl___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimprocDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 139, 147, 138, 247, 237, 61, 250)}};
static const lean_object* l_Lean_Fmt_fmtSimprocDecl___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimprocDecl___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtSimprocDecl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 181, 242, 173, 159, 205, 225, 247)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDSimprocDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "command_Dsimproc_decl_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtDSimprocDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDSimprocDecl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDSimprocDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDSimprocDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDSimprocDecl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDSimprocDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDSimprocDecl___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDSimprocDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 5, 118, 89, 162, 130, 40, 80)}};
static const lean_object* l_Lean_Fmt_fmtDSimprocDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDSimprocDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimprocDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimprocDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtDSimprocDecl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 144, 194, 212, 213, 214, 98, 60)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "command__Builtin_simproc__[_]_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtBuiltinSimproc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSimproc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimproc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimproc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimproc___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimproc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimproc___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinSimproc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 226, 216, 188, 254, 131, 81, 168)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinSimproc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSimproc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimproc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtBuiltinSimproc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 180, 89, 134, 78, 140, 114, 144)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinDSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "command__Builtin_dsimproc__[_]_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtBuiltinDSimproc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinDSimproc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinDSimproc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinDSimproc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinDSimproc___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinDSimproc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinDSimproc___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinDSimproc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 5, 95, 80, 27, 210, 221, 36)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinDSimproc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinDSimproc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinDSimproc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtBuiltinDSimproc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 82, 98, 67, 64, 2, 128, 246)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "command_Builtin_simproc_decl_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 244, 85, 86, 69, 85, 20, 202)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtBuiltinSimprocDecl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 26, 111, 247, 40, 0, 18, 166)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "command_Builtin_dsimproc_decl_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 226, 173, 154, 110, 51, 239, 123)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinDSimprocDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinDSimprocDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtBuiltinDSimprocDecl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 85, 91, 82, 150, 41, 6, 161)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simprocPattern"};
static const lean_object* l_Lean_Fmt_fmtSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimprocPattern___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimprocPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimprocPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimprocPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimprocPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 202, 22, 200, 44, 153, 152, 252)}};
static const lean_object* l_Lean_Fmt_fmtSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimprocPattern___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocPattern___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtSimprocPattern"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 34, 162, 9, 232, 205, 182, 105)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "simprocPatternBuiltin"};
static const lean_object* l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 222, 179, 10, 105, 49, 55, 147)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocPattern___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtBuiltinSimprocPattern"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 150, 97, 64, 18, 218, 206, 194)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Fmt_fmtSimprocAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simprocAttr"};
static const lean_object* l_Lean_Fmt_fmtSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimprocAttr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimprocAttr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimprocAttr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimprocAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 18, 96, 241, 98, 31, 116, 164)}};
static const lean_object* l_Lean_Fmt_fmtSimprocAttr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtSimprocAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 169, 241, 246, 182, 150, 64, 130)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSevalprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sevalprocAttr"};
static const lean_object* l_Lean_Fmt_fmtSevalprocAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSevalprocAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSevalprocAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSevalprocAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSevalprocAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSevalprocAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSevalprocAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtSevalprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSevalprocAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSevalprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 11, 137, 55, 180, 134, 243, 204)}};
static const lean_object* l_Lean_Fmt_fmtSevalprocAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSevalprocAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSevalprocAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSevalprocAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtSevalprocAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 179, 110, 98, 189, 113, 83, 204)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "simprocBuiltinAttr"};
static const lean_object* l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 10, 79, 178, 22, 57, 41, 253)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtBuiltinSimprocAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 121, 216, 162, 138, 157, 88, 169)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sevalprocBuiltinAttr"};
static const lean_object* l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 215, 225, 250, 188, 171, 99, 207)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSevalprocAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSevalprocAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtBuiltinSevalprocAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 178, 219, 243, 193, 198, 19, 129)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocLike(lean_object* v_docComment_x3f_10_, lean_object* v_mods_11_, lean_object* v_simprocTk_12_, lean_object* v_phase_x3f_13_, lean_object* v_lbTk_x3f_14_, lean_object* v_ids_x3f_15_, lean_object* v_rbTk_x3f_16_, lean_object* v_declId_17_, lean_object* v_lparenTk_18_, lean_object* v_trigger_19_, lean_object* v_rparenTk_20_, lean_object* v_colonEqTk_21_, lean_object* v_body_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Fmt_fmt(v_simprocTk_12_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; lean_object* v_a_27_; lean_object* v___x_28_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_a_26_);
v_a_27_ = lean_ctor_get(v___x_25_, 1);
lean_inc(v_a_27_);
lean_dec_ref_known(v___x_25_, 2);
v___x_28_ = l_Lean_Fmt_fmt_x3f(v_phase_x3f_13_, v_a_23_, v_a_27_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_31_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
lean_inc(v_a_30_);
lean_dec_ref_known(v___x_28_, 2);
v___x_31_ = l_Lean_Fmt_fmt_x3f(v_lbTk_x3f_14_, v_a_23_, v_a_30_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v_a_33_; lean_object* v___x_34_; lean_object* v___y_36_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_a_32_);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
lean_inc(v_a_33_);
lean_dec_ref_known(v___x_31_, 2);
v___x_34_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocLike___closed__0));
if (lean_obj_tag(v_ids_x3f_15_) == 0)
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocLike___closed__3));
v___y_36_ = v___x_96_;
goto v___jp_35_;
}
else
{
lean_object* v_val_97_; 
v_val_97_ = lean_ctor_get(v_ids_x3f_15_, 0);
lean_inc(v_val_97_);
lean_dec_ref_known(v_ids_x3f_15_, 1);
v___y_36_ = v_val_97_;
goto v___jp_35_;
}
v___jp_35_:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_36_, v_a_23_, v_a_33_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; lean_object* v_a_39_; lean_object* v___x_40_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_a_38_);
v_a_39_ = lean_ctor_get(v___x_37_, 1);
lean_inc(v_a_39_);
lean_dec_ref_known(v___x_37_, 2);
v___x_40_ = l_Lean_Fmt_fmt_x3f(v_rbTk_x3f_16_, v_a_23_, v_a_39_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v_a_42_; lean_object* v___x_43_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_a_41_);
v_a_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc(v_a_42_);
lean_dec_ref_known(v___x_40_, 2);
v___x_43_ = l_Lean_Fmt_fmt(v_declId_17_, v_a_23_, v_a_42_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v_a_44_; lean_object* v_a_45_; lean_object* v___x_46_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_a_44_);
v_a_45_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_43_, 2);
v___x_46_ = l_Lean_Fmt_fmt(v_lparenTk_18_, v_a_23_, v_a_45_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v_a_48_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
v_a_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_46_, 2);
v___x_49_ = l_Lean_Fmt_fmt(v_trigger_19_, v_a_23_, v_a_48_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v___x_52_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
v_a_51_ = lean_ctor_get(v___x_49_, 1);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_49_, 2);
v___x_52_ = l_Lean_Fmt_fmt(v_rparenTk_20_, v_a_23_, v_a_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v___x_55_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
v_a_54_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_52_, 2);
v___x_55_ = l_Lean_Fmt_fmt(v_colonEqTk_21_, v_a_23_, v_a_54_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v_a_57_; lean_object* v___x_58_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_56_);
v_a_57_ = lean_ctor_get(v___x_55_, 1);
lean_inc(v_a_57_);
lean_dec_ref_known(v___x_55_, 2);
v___x_58_ = l_Lean_Fmt_fmt(v_body_22_, v_a_23_, v_a_57_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v_a_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
v_a_60_ = lean_ctor_get(v___x_58_, 1);
lean_inc(v_a_60_);
lean_dec_ref_known(v___x_58_, 2);
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_mk_empty_array_with_capacity(v___x_61_);
lean_inc_ref(v___x_62_);
v___x_63_ = lean_array_push(v___x_62_, v_a_26_);
v___x_64_ = lean_array_push(v___x_63_, v_a_29_);
v___x_65_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_64_);
lean_dec_ref(v___x_64_);
v___x_66_ = 0;
v___x_67_ = 1;
v___x_68_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocLike___closed__1));
v___x_69_ = l_Lean_Fmt_Layouts_collection(v___x_34_, v_a_32_, v_a_38_, v_a_41_, v___x_68_);
lean_dec(v_a_38_);
v___x_70_ = l_Lean_Fmt_Layouts_parens(v_a_47_, v_a_50_, v_a_53_);
v___x_71_ = lean_array_push(v___x_62_, v_a_44_);
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
v___x_73_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocLike___closed__2));
v___x_74_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_72_, v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_65_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_67_);
v___x_76_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_69_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_67_);
v___x_77_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_67_);
v___x_78_ = lean_unsigned_to_nat(3u);
v___x_79_ = lean_mk_empty_array_with_capacity(v___x_78_);
v___x_80_ = lean_array_push(v___x_79_, v___x_75_);
v___x_81_ = lean_array_push(v___x_80_, v___x_76_);
v___x_82_ = lean_array_push(v___x_81_, v___x_77_);
v___x_83_ = l_Lean_Fmt_Layouts_blocks(v___x_82_, v___x_67_);
lean_dec_ref(v___x_82_);
v___x_84_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_83_, v_a_56_, v_a_59_, v___x_66_);
v___x_85_ = lean_box(0);
v___x_86_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_10_, v___x_85_, v_mods_11_, v___x_84_, v_a_23_, v_a_60_);
return v___x_86_;
}
else
{
lean_dec(v_a_56_);
lean_dec(v_a_53_);
lean_dec(v_a_50_);
lean_dec(v_a_47_);
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v_a_38_);
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_docComment_x3f_10_);
return v___x_58_;
}
}
else
{
lean_dec(v_a_53_);
lean_dec(v_a_50_);
lean_dec(v_a_47_);
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v_a_38_);
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_docComment_x3f_10_);
return v___x_55_;
}
}
else
{
lean_dec(v_a_50_);
lean_dec(v_a_47_);
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v_a_38_);
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_docComment_x3f_10_);
return v___x_52_;
}
}
else
{
lean_dec(v_a_47_);
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v_a_38_);
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_rparenTk_20_);
lean_dec(v_docComment_x3f_10_);
return v___x_49_;
}
}
else
{
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v_a_38_);
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_rparenTk_20_);
lean_dec(v_trigger_19_);
lean_dec(v_docComment_x3f_10_);
return v___x_46_;
}
}
else
{
lean_dec(v_a_41_);
lean_dec(v_a_38_);
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_rparenTk_20_);
lean_dec(v_trigger_19_);
lean_dec(v_lparenTk_18_);
lean_dec(v_docComment_x3f_10_);
return v___x_43_;
}
}
else
{
lean_dec(v_a_38_);
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_rparenTk_20_);
lean_dec(v_trigger_19_);
lean_dec(v_lparenTk_18_);
lean_dec(v_declId_17_);
lean_dec(v_docComment_x3f_10_);
return v___x_40_;
}
}
else
{
lean_object* v_a_87_; lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
lean_dec(v_a_32_);
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_rparenTk_20_);
lean_dec(v_trigger_19_);
lean_dec(v_lparenTk_18_);
lean_dec(v_declId_17_);
lean_dec(v_rbTk_x3f_16_);
lean_dec(v_docComment_x3f_10_);
v_a_87_ = lean_ctor_get(v___x_37_, 0);
v_a_88_ = lean_ctor_get(v___x_37_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_37_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_inc(v_a_87_);
lean_dec(v___x_37_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_87_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
else
{
lean_dec(v_a_29_);
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_rparenTk_20_);
lean_dec(v_trigger_19_);
lean_dec(v_lparenTk_18_);
lean_dec(v_declId_17_);
lean_dec(v_rbTk_x3f_16_);
lean_dec(v_ids_x3f_15_);
lean_dec(v_docComment_x3f_10_);
return v___x_31_;
}
}
else
{
lean_dec(v_a_26_);
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_rparenTk_20_);
lean_dec(v_trigger_19_);
lean_dec(v_lparenTk_18_);
lean_dec(v_declId_17_);
lean_dec(v_rbTk_x3f_16_);
lean_dec(v_ids_x3f_15_);
lean_dec(v_lbTk_x3f_14_);
lean_dec(v_docComment_x3f_10_);
return v___x_28_;
}
}
else
{
lean_dec(v_body_22_);
lean_dec(v_colonEqTk_21_);
lean_dec(v_rparenTk_20_);
lean_dec(v_trigger_19_);
lean_dec(v_lparenTk_18_);
lean_dec(v_declId_17_);
lean_dec(v_rbTk_x3f_16_);
lean_dec(v_ids_x3f_15_);
lean_dec(v_lbTk_x3f_14_);
lean_dec(v_phase_x3f_13_);
lean_dec(v_docComment_x3f_10_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocLike___boxed(lean_object* v_docComment_x3f_98_, lean_object* v_mods_99_, lean_object* v_simprocTk_100_, lean_object* v_phase_x3f_101_, lean_object* v_lbTk_x3f_102_, lean_object* v_ids_x3f_103_, lean_object* v_rbTk_x3f_104_, lean_object* v_declId_105_, lean_object* v_lparenTk_106_, lean_object* v_trigger_107_, lean_object* v_rparenTk_108_, lean_object* v_colonEqTk_109_, lean_object* v_body_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Fmt_fmtSimprocLike(v_docComment_x3f_98_, v_mods_99_, v_simprocTk_100_, v_phase_x3f_101_, v_lbTk_x3f_102_, v_ids_x3f_103_, v_rbTk_x3f_104_, v_declId_105_, v_lparenTk_106_, v_trigger_107_, v_rparenTk_108_, v_colonEqTk_109_, v_body_110_, v_a_111_, v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec_ref(v_mods_99_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocPatternLike(lean_object* v_simprocPatternTk_114_, lean_object* v_pattern_115_, lean_object* v_arrowTk_116_, lean_object* v_declId_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Fmt_fmt(v_simprocPatternTk_114_, v_a_118_, v_a_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_123_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
v_a_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_a_122_);
lean_dec_ref_known(v___x_120_, 2);
v___x_123_ = l_Lean_Fmt_fmt(v_pattern_115_, v_a_118_, v_a_122_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v_a_125_; lean_object* v___x_126_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
v_a_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_123_, 2);
v___x_126_ = l_Lean_Fmt_fmt(v_arrowTk_116_, v_a_118_, v_a_125_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v_a_128_; lean_object* v___x_129_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
v_a_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_126_, 2);
v___x_129_ = l_Lean_Fmt_fmt(v_declId_117_, v_a_118_, v_a_128_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_146_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_a_131_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_146_ == 0)
{
v___x_133_ = v___x_129_;
v_isShared_134_ = v_isSharedCheck_146_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_146_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_135_ = 0;
v___x_136_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_124_, v_a_127_, v_a_130_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_mk_empty_array_with_capacity(v___x_137_);
v___x_139_ = lean_array_push(v___x_138_, v_a_121_);
v___x_140_ = lean_array_push(v___x_139_, v___x_136_);
v___x_141_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocLike___closed__2));
v___x_142_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_140_, v___x_141_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_142_);
v___x_144_ = v___x_133_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_a_131_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_dec(v_a_127_);
lean_dec(v_a_124_);
lean_dec(v_a_121_);
return v___x_129_;
}
}
else
{
lean_dec(v_a_124_);
lean_dec(v_a_121_);
lean_dec(v_declId_117_);
return v___x_126_;
}
}
else
{
lean_dec(v_a_121_);
lean_dec(v_declId_117_);
lean_dec(v_arrowTk_116_);
return v___x_123_;
}
}
else
{
lean_dec(v_declId_117_);
lean_dec(v_arrowTk_116_);
lean_dec(v_pattern_115_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocPatternLike___boxed(lean_object* v_simprocPatternTk_147_, lean_object* v_pattern_148_, lean_object* v_arrowTk_149_, lean_object* v_declId_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Fmt_fmtSimprocPatternLike(v_simprocPatternTk_147_, v_pattern_148_, v_arrowTk_149_, v_declId_150_, v_a_151_, v_a_152_);
lean_dec_ref(v_a_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocAttrLike(lean_object* v_simprocTk_154_, lean_object* v_phase_x3f_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Fmt_fmt(v_simprocTk_154_, v_a_156_, v_a_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v_a_160_; lean_object* v___x_161_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
v_a_160_ = lean_ctor_get(v___x_158_, 1);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_158_, 2);
v___x_161_ = l_Lean_Fmt_fmt_x3f(v_phase_x3f_155_, v_a_156_, v_a_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_175_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_a_163_ = lean_ctor_get(v___x_161_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_175_ == 0)
{
v___x_165_ = v___x_161_;
v_isShared_166_ = v_isSharedCheck_175_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_175_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_167_ = lean_unsigned_to_nat(2u);
v___x_168_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_169_ = lean_array_push(v___x_168_, v_a_159_);
v___x_170_ = lean_array_push(v___x_169_, v_a_162_);
v___x_171_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_170_);
lean_dec_ref(v___x_170_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_171_);
v___x_173_ = v___x_165_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_a_163_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
else
{
lean_dec(v_a_159_);
return v___x_161_;
}
}
else
{
lean_dec(v_phase_x3f_155_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocAttrLike___boxed(lean_object* v_simprocTk_176_, lean_object* v_phase_x3f_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Fmt_fmtSimprocAttrLike(v_simprocTk_176_, v_phase_x3f_177_, v_a_178_, v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimproc(lean_object* v_x_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v_lbTk_x3f_214_; lean_object* v_ids_x3f_215_; lean_object* v_rbTk_x3f_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__5));
lean_inc(v_x_205_);
v___x_250_ = l_Lean_Syntax_isOfKind(v_x_205_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_x_205_);
v___x_251_ = l_Lean_Fmt_Error_partialFormatter;
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_a_207_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v_phase_x3f_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v_docComment_x3f_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_299_ = l_Lean_Syntax_getArg(v_x_205_, v___x_253_);
v___x_300_ = l_Lean_Syntax_isNone(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_299_);
v___x_302_ = l_Lean_Syntax_matchesNull(v___x_299_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v___x_299_);
lean_dec(v_x_205_);
v___x_303_ = l_Lean_Fmt_Error_partialFormatter;
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v_a_207_);
return v___x_304_;
}
else
{
lean_object* v_docComment_x3f_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_docComment_x3f_305_ = l_Lean_Syntax_getArg(v___x_299_, v___x_253_);
lean_dec(v___x_299_);
v___x_306_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__11));
lean_inc(v_docComment_x3f_305_);
v___x_307_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_docComment_x3f_305_);
lean_dec(v_x_205_);
v___x_308_ = l_Lean_Fmt_Error_partialFormatter;
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_a_207_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_docComment_x3f_305_);
v_docComment_x3f_279_ = v___x_310_;
v___y_280_ = v_a_206_;
v___y_281_ = v_a_207_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v___x_311_; 
lean_dec(v___x_299_);
v___x_311_ = lean_box(0);
v_docComment_x3f_279_ = v___x_311_;
v___y_280_ = v_a_206_;
v___y_281_ = v_a_207_;
goto v___jp_278_;
}
v___jp_254_:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_unsigned_to_nat(4u);
v___x_265_ = l_Lean_Syntax_getArg(v_x_205_, v___x_264_);
v___x_266_ = l_Lean_Syntax_isNone(v___x_265_);
if (v___x_266_ == 0)
{
uint8_t v___x_267_; 
lean_inc(v___x_265_);
v___x_267_ = l_Lean_Syntax_matchesNull(v___x_265_, v___y_256_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v___x_265_);
lean_dec(v_phase_x3f_261_);
lean_dec(v___y_260_);
lean_dec(v___y_259_);
lean_dec(v___y_258_);
lean_dec(v_x_205_);
v___x_268_ = l_Lean_Fmt_Error_partialFormatter;
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___y_263_);
return v___x_269_;
}
else
{
lean_object* v_lbTk_x3f_270_; lean_object* v___x_271_; lean_object* v_rbTk_x3f_272_; lean_object* v_ids_x3f_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_lbTk_x3f_270_ = l_Lean_Syntax_getArg(v___x_265_, v___x_253_);
v___x_271_ = l_Lean_Syntax_getArg(v___x_265_, v___y_255_);
v_rbTk_x3f_272_ = l_Lean_Syntax_getArg(v___x_265_, v___y_257_);
lean_dec(v___x_265_);
v_ids_x3f_273_ = l_Lean_Syntax_getArgs(v___x_271_);
lean_dec(v___x_271_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_lbTk_x3f_270_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_ids_x3f_273_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v_rbTk_x3f_272_);
v___y_209_ = v___y_255_;
v___y_210_ = v___y_258_;
v___y_211_ = v___y_260_;
v___y_212_ = v___y_259_;
v___y_213_ = v_phase_x3f_261_;
v_lbTk_x3f_214_ = v___x_274_;
v_ids_x3f_215_ = v___x_275_;
v_rbTk_x3f_216_ = v___x_276_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
goto v___jp_208_;
}
}
else
{
lean_object* v___x_277_; 
lean_dec(v___x_265_);
v___x_277_ = lean_box(0);
v___y_209_ = v___y_255_;
v___y_210_ = v___y_258_;
v___y_211_ = v___y_260_;
v___y_212_ = v___y_259_;
v___y_213_ = v_phase_x3f_261_;
v_lbTk_x3f_214_ = v___x_277_;
v_ids_x3f_215_ = v___x_277_;
v_rbTk_x3f_216_ = v___x_277_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
goto v___jp_208_;
}
}
v___jp_278_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = l_Lean_Syntax_getArg(v_x_205_, v___x_282_);
v___x_284_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__8));
lean_inc(v___x_283_);
v___x_285_ = l_Lean_Syntax_isOfKind(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v___x_283_);
lean_dec(v_docComment_x3f_279_);
lean_dec(v_x_205_);
v___x_286_ = l_Lean_Fmt_Error_partialFormatter;
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___y_281_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v_simprocTk_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_288_ = lean_unsigned_to_nat(2u);
v_simprocTk_289_ = l_Lean_Syntax_getArg(v_x_205_, v___x_288_);
v___x_290_ = lean_unsigned_to_nat(3u);
v___x_291_ = l_Lean_Syntax_getArg(v_x_205_, v___x_290_);
v___x_292_ = l_Lean_Syntax_isNone(v___x_291_);
if (v___x_292_ == 0)
{
uint8_t v___x_293_; 
lean_inc(v___x_291_);
v___x_293_ = l_Lean_Syntax_matchesNull(v___x_291_, v___x_282_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v___x_291_);
lean_dec(v_simprocTk_289_);
lean_dec(v___x_283_);
lean_dec(v_docComment_x3f_279_);
lean_dec(v_x_205_);
v___x_294_ = l_Lean_Fmt_Error_partialFormatter;
v___x_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___y_281_);
return v___x_295_;
}
else
{
lean_object* v_phase_x3f_296_; lean_object* v___x_297_; 
v_phase_x3f_296_ = l_Lean_Syntax_getArg(v___x_291_, v___x_253_);
lean_dec(v___x_291_);
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_phase_x3f_296_);
v___y_255_ = v___x_282_;
v___y_256_ = v___x_290_;
v___y_257_ = v___x_288_;
v___y_258_ = v_docComment_x3f_279_;
v___y_259_ = v___x_283_;
v___y_260_ = v_simprocTk_289_;
v_phase_x3f_261_ = v___x_297_;
v___y_262_ = v___y_280_;
v___y_263_ = v___y_281_;
goto v___jp_254_;
}
}
else
{
lean_object* v___x_298_; 
lean_dec(v___x_291_);
v___x_298_ = lean_box(0);
v___y_255_ = v___x_282_;
v___y_256_ = v___x_290_;
v___y_257_ = v___x_288_;
v___y_258_ = v_docComment_x3f_279_;
v___y_259_ = v___x_283_;
v___y_260_ = v_simprocTk_289_;
v_phase_x3f_261_ = v___x_298_;
v___y_262_ = v___y_280_;
v___y_263_ = v___y_281_;
goto v___jp_254_;
}
}
}
}
v___jp_208_:
{
lean_object* v___x_219_; lean_object* v_declId_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_219_ = lean_unsigned_to_nat(5u);
v_declId_220_ = l_Lean_Syntax_getArg(v_x_205_, v___x_219_);
v___x_221_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_220_);
v___x_222_ = l_Lean_Syntax_isOfKind(v_declId_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_declId_220_);
lean_dec(v_rbTk_x3f_216_);
lean_dec(v_ids_x3f_215_);
lean_dec(v_lbTk_x3f_214_);
lean_dec(v___y_213_);
lean_dec(v___y_212_);
lean_dec(v___y_211_);
lean_dec(v___y_210_);
lean_dec(v_x_205_);
v___x_223_ = l_Lean_Fmt_Error_partialFormatter;
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___y_218_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v_lparenTk_226_; lean_object* v___x_227_; lean_object* v_trigger_228_; lean_object* v___x_229_; lean_object* v_rparenTk_230_; lean_object* v___x_231_; lean_object* v_colonEqTk_232_; lean_object* v___x_233_; lean_object* v_body_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_225_ = lean_unsigned_to_nat(6u);
v_lparenTk_226_ = l_Lean_Syntax_getArg(v_x_205_, v___x_225_);
v___x_227_ = lean_unsigned_to_nat(7u);
v_trigger_228_ = l_Lean_Syntax_getArg(v_x_205_, v___x_227_);
v___x_229_ = lean_unsigned_to_nat(8u);
v_rparenTk_230_ = l_Lean_Syntax_getArg(v_x_205_, v___x_229_);
v___x_231_ = lean_unsigned_to_nat(9u);
v_colonEqTk_232_ = l_Lean_Syntax_getArg(v_x_205_, v___x_231_);
v___x_233_ = lean_unsigned_to_nat(10u);
v_body_234_ = l_Lean_Syntax_getArg(v_x_205_, v___x_233_);
lean_dec(v_x_205_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___y_212_);
v___x_236_ = lean_mk_empty_array_with_capacity(v___y_209_);
v___x_237_ = lean_array_push(v___x_236_, v___x_235_);
if (lean_obj_tag(v___y_213_) == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = l_Lean_Fmt_fmtSimprocLike(v___y_210_, v___x_237_, v___y_211_, v___x_238_, v_lbTk_x3f_214_, v_ids_x3f_215_, v_rbTk_x3f_216_, v_declId_220_, v_lparenTk_226_, v_trigger_228_, v_rparenTk_230_, v_colonEqTk_232_, v_body_234_, v___y_217_, v___y_218_);
lean_dec_ref(v___x_237_);
return v___x_239_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_val_240_ = lean_ctor_get(v___y_213_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___y_213_);
if (v_isSharedCheck_248_ == 0)
{
v___x_242_ = v___y_213_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_dec(v___y_213_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_val_240_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Fmt_fmtSimprocLike(v___y_210_, v___x_237_, v___y_211_, v___x_245_, v_lbTk_x3f_214_, v_ids_x3f_215_, v_rbTk_x3f_216_, v_declId_220_, v_lparenTk_226_, v_trigger_228_, v_rparenTk_230_, v_colonEqTk_232_, v_body_234_, v___y_217_, v___y_218_);
lean_dec_ref(v___x_237_);
return v___x_246_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimproc___boxed(lean_object* v_x_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Fmt_fmtSimproc(v_x_312_, v_a_313_, v_a_314_);
lean_dec_ref(v_a_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1(){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_323_ = l_Lean_Fmt_fmtAttribute;
v___x_324_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__5));
v___x_325_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___closed__2));
v___x_326_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimproc___boxed), 3, 0);
v___x_327_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_323_, v___x_324_, v___x_325_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1___boxed(lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1();
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimproc(lean_object* v_x_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v_lbTk_x3f_344_; lean_object* v_ids_x3f_345_; lean_object* v_rbTk_x3f_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_Fmt_fmtDSimproc___closed__1));
lean_inc(v_x_335_);
v___x_380_ = l_Lean_Syntax_isOfKind(v_x_335_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_x_335_);
v___x_381_ = l_Lean_Fmt_Error_partialFormatter;
v___x_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_337_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v_phase_x3f_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v_docComment_x3f_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_429_ = l_Lean_Syntax_getArg(v_x_335_, v___x_383_);
v___x_430_ = l_Lean_Syntax_isNone(v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_429_);
v___x_432_ = l_Lean_Syntax_matchesNull(v___x_429_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v___x_429_);
lean_dec(v_x_335_);
v___x_433_ = l_Lean_Fmt_Error_partialFormatter;
v___x_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_a_337_);
return v___x_434_;
}
else
{
lean_object* v_docComment_x3f_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_docComment_x3f_435_ = l_Lean_Syntax_getArg(v___x_429_, v___x_383_);
lean_dec(v___x_429_);
v___x_436_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__11));
lean_inc(v_docComment_x3f_435_);
v___x_437_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v_docComment_x3f_435_);
lean_dec(v_x_335_);
v___x_438_ = l_Lean_Fmt_Error_partialFormatter;
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_a_337_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v_docComment_x3f_435_);
v_docComment_x3f_409_ = v___x_440_;
v___y_410_ = v_a_336_;
v___y_411_ = v_a_337_;
goto v___jp_408_;
}
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v___x_429_);
v___x_441_ = lean_box(0);
v_docComment_x3f_409_ = v___x_441_;
v___y_410_ = v_a_336_;
v___y_411_ = v_a_337_;
goto v___jp_408_;
}
v___jp_384_:
{
lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_394_ = lean_unsigned_to_nat(4u);
v___x_395_ = l_Lean_Syntax_getArg(v_x_335_, v___x_394_);
v___x_396_ = l_Lean_Syntax_isNone(v___x_395_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
lean_inc(v___x_395_);
v___x_397_ = l_Lean_Syntax_matchesNull(v___x_395_, v___y_387_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v___x_395_);
lean_dec(v_phase_x3f_391_);
lean_dec(v___y_390_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v_x_335_);
v___x_398_ = l_Lean_Fmt_Error_partialFormatter;
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___y_393_);
return v___x_399_;
}
else
{
lean_object* v_lbTk_x3f_400_; lean_object* v___x_401_; lean_object* v_rbTk_x3f_402_; lean_object* v_ids_x3f_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_lbTk_x3f_400_ = l_Lean_Syntax_getArg(v___x_395_, v___x_383_);
v___x_401_ = l_Lean_Syntax_getArg(v___x_395_, v___y_389_);
v_rbTk_x3f_402_ = l_Lean_Syntax_getArg(v___x_395_, v___y_388_);
lean_dec(v___x_395_);
v_ids_x3f_403_ = l_Lean_Syntax_getArgs(v___x_401_);
lean_dec(v___x_401_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v_lbTk_x3f_400_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v_ids_x3f_403_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_rbTk_x3f_402_);
v___y_339_ = v___y_385_;
v___y_340_ = v___y_386_;
v___y_341_ = v_phase_x3f_391_;
v___y_342_ = v___y_389_;
v___y_343_ = v___y_390_;
v_lbTk_x3f_344_ = v___x_404_;
v_ids_x3f_345_ = v___x_405_;
v_rbTk_x3f_346_ = v___x_406_;
v___y_347_ = v___y_392_;
v___y_348_ = v___y_393_;
goto v___jp_338_;
}
}
else
{
lean_object* v___x_407_; 
lean_dec(v___x_395_);
v___x_407_ = lean_box(0);
v___y_339_ = v___y_385_;
v___y_340_ = v___y_386_;
v___y_341_ = v_phase_x3f_391_;
v___y_342_ = v___y_389_;
v___y_343_ = v___y_390_;
v_lbTk_x3f_344_ = v___x_407_;
v_ids_x3f_345_ = v___x_407_;
v_rbTk_x3f_346_ = v___x_407_;
v___y_347_ = v___y_392_;
v___y_348_ = v___y_393_;
goto v___jp_338_;
}
}
v___jp_408_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = l_Lean_Syntax_getArg(v_x_335_, v___x_412_);
v___x_414_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__8));
lean_inc(v___x_413_);
v___x_415_ = l_Lean_Syntax_isOfKind(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v___x_413_);
lean_dec(v_docComment_x3f_409_);
lean_dec(v_x_335_);
v___x_416_ = l_Lean_Fmt_Error_partialFormatter;
v___x_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___y_411_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v_dsimprocTk_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_418_ = lean_unsigned_to_nat(2u);
v_dsimprocTk_419_ = l_Lean_Syntax_getArg(v_x_335_, v___x_418_);
v___x_420_ = lean_unsigned_to_nat(3u);
v___x_421_ = l_Lean_Syntax_getArg(v_x_335_, v___x_420_);
v___x_422_ = l_Lean_Syntax_isNone(v___x_421_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
lean_inc(v___x_421_);
v___x_423_ = l_Lean_Syntax_matchesNull(v___x_421_, v___x_412_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v___x_421_);
lean_dec(v_dsimprocTk_419_);
lean_dec(v___x_413_);
lean_dec(v_docComment_x3f_409_);
lean_dec(v_x_335_);
v___x_424_ = l_Lean_Fmt_Error_partialFormatter;
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___y_411_);
return v___x_425_;
}
else
{
lean_object* v_phase_x3f_426_; lean_object* v___x_427_; 
v_phase_x3f_426_ = l_Lean_Syntax_getArg(v___x_421_, v___x_383_);
lean_dec(v___x_421_);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_phase_x3f_426_);
v___y_385_ = v___x_413_;
v___y_386_ = v_dsimprocTk_419_;
v___y_387_ = v___x_420_;
v___y_388_ = v___x_418_;
v___y_389_ = v___x_412_;
v___y_390_ = v_docComment_x3f_409_;
v_phase_x3f_391_ = v___x_427_;
v___y_392_ = v___y_410_;
v___y_393_ = v___y_411_;
goto v___jp_384_;
}
}
else
{
lean_object* v___x_428_; 
lean_dec(v___x_421_);
v___x_428_ = lean_box(0);
v___y_385_ = v___x_413_;
v___y_386_ = v_dsimprocTk_419_;
v___y_387_ = v___x_420_;
v___y_388_ = v___x_418_;
v___y_389_ = v___x_412_;
v___y_390_ = v_docComment_x3f_409_;
v_phase_x3f_391_ = v___x_428_;
v___y_392_ = v___y_410_;
v___y_393_ = v___y_411_;
goto v___jp_384_;
}
}
}
}
v___jp_338_:
{
lean_object* v___x_349_; lean_object* v_declId_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_349_ = lean_unsigned_to_nat(5u);
v_declId_350_ = l_Lean_Syntax_getArg(v_x_335_, v___x_349_);
v___x_351_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_350_);
v___x_352_ = l_Lean_Syntax_isOfKind(v_declId_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_declId_350_);
lean_dec(v_rbTk_x3f_346_);
lean_dec(v_ids_x3f_345_);
lean_dec(v_lbTk_x3f_344_);
lean_dec(v___y_343_);
lean_dec(v___y_341_);
lean_dec(v___y_340_);
lean_dec(v___y_339_);
lean_dec(v_x_335_);
v___x_353_ = l_Lean_Fmt_Error_partialFormatter;
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___y_348_);
return v___x_354_;
}
else
{
lean_object* v___x_355_; lean_object* v_lparenTk_356_; lean_object* v___x_357_; lean_object* v_trigger_358_; lean_object* v___x_359_; lean_object* v_rparenTk_360_; lean_object* v___x_361_; lean_object* v_colonEqTk_362_; lean_object* v___x_363_; lean_object* v_body_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_355_ = lean_unsigned_to_nat(6u);
v_lparenTk_356_ = l_Lean_Syntax_getArg(v_x_335_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(7u);
v_trigger_358_ = l_Lean_Syntax_getArg(v_x_335_, v___x_357_);
v___x_359_ = lean_unsigned_to_nat(8u);
v_rparenTk_360_ = l_Lean_Syntax_getArg(v_x_335_, v___x_359_);
v___x_361_ = lean_unsigned_to_nat(9u);
v_colonEqTk_362_ = l_Lean_Syntax_getArg(v_x_335_, v___x_361_);
v___x_363_ = lean_unsigned_to_nat(10u);
v_body_364_ = l_Lean_Syntax_getArg(v_x_335_, v___x_363_);
lean_dec(v_x_335_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v___y_339_);
v___x_366_ = lean_mk_empty_array_with_capacity(v___y_342_);
v___x_367_ = lean_array_push(v___x_366_, v___x_365_);
if (lean_obj_tag(v___y_341_) == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_box(0);
v___x_369_ = l_Lean_Fmt_fmtSimprocLike(v___y_343_, v___x_367_, v___y_340_, v___x_368_, v_lbTk_x3f_344_, v_ids_x3f_345_, v_rbTk_x3f_346_, v_declId_350_, v_lparenTk_356_, v_trigger_358_, v_rparenTk_360_, v_colonEqTk_362_, v_body_364_, v___y_347_, v___y_348_);
lean_dec_ref(v___x_367_);
return v___x_369_;
}
else
{
lean_object* v_val_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_val_370_ = lean_ctor_get(v___y_341_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___y_341_);
if (v_isSharedCheck_378_ == 0)
{
v___x_372_ = v___y_341_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_val_370_);
lean_dec(v___y_341_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_val_370_);
v___x_375_ = v_reuseFailAlloc_377_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Fmt_fmtSimprocLike(v___y_343_, v___x_367_, v___y_340_, v___x_375_, v_lbTk_x3f_344_, v_ids_x3f_345_, v_rbTk_x3f_346_, v_declId_350_, v_lparenTk_356_, v_trigger_358_, v_rparenTk_360_, v_colonEqTk_362_, v_body_364_, v___y_347_, v___y_348_);
lean_dec_ref(v___x_367_);
return v___x_376_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimproc___boxed(lean_object* v_x_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Fmt_fmtDSimproc(v_x_442_, v_a_443_, v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1(){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_452_ = l_Lean_Fmt_fmtAttribute;
v___x_453_ = ((lean_object*)(l_Lean_Fmt_fmtDSimproc___closed__1));
v___x_454_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___closed__1));
v___x_455_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDSimproc___boxed), 3, 0);
v___x_456_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_452_, v___x_453_, v___x_454_, v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1___boxed(lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1();
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocDecl(lean_object* v_x_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_docComment_x3f_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocDecl___closed__2));
lean_inc(v_x_466_);
v___x_495_ = l_Lean_Syntax_isOfKind(v_x_466_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_x_466_);
v___x_496_ = l_Lean_Fmt_Error_partialFormatter;
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_a_468_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = l_Lean_Syntax_getArg(v_x_466_, v___x_498_);
v___x_500_ = l_Lean_Syntax_isNone(v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_499_);
v___x_502_ = l_Lean_Syntax_matchesNull(v___x_499_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v___x_499_);
lean_dec(v_x_466_);
v___x_503_ = l_Lean_Fmt_Error_partialFormatter;
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_a_468_);
return v___x_504_;
}
else
{
lean_object* v_docComment_x3f_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_docComment_x3f_505_ = l_Lean_Syntax_getArg(v___x_499_, v___x_498_);
lean_dec(v___x_499_);
v___x_506_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__11));
lean_inc(v_docComment_x3f_505_);
v___x_507_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_docComment_x3f_505_);
lean_dec(v_x_466_);
v___x_508_ = l_Lean_Fmt_Error_partialFormatter;
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_a_468_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v_docComment_x3f_505_);
v_docComment_x3f_470_ = v___x_510_;
v___y_471_ = v_a_467_;
v___y_472_ = v_a_468_;
goto v___jp_469_;
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec(v___x_499_);
v___x_511_ = lean_box(0);
v_docComment_x3f_470_ = v___x_511_;
v___y_471_ = v_a_467_;
v___y_472_ = v_a_468_;
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_473_; lean_object* v_declId_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_473_ = lean_unsigned_to_nat(2u);
v_declId_474_ = l_Lean_Syntax_getArg(v_x_466_, v___x_473_);
v___x_475_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_474_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_declId_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_declId_474_);
lean_dec(v_docComment_x3f_470_);
lean_dec(v_x_466_);
v___x_477_ = l_Lean_Fmt_Error_partialFormatter;
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___y_472_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v_simprocDeclTk_480_; lean_object* v___x_481_; lean_object* v_lparenTk_482_; lean_object* v___x_483_; lean_object* v_trigger_484_; lean_object* v___x_485_; lean_object* v_rparenTk_486_; lean_object* v___x_487_; lean_object* v_colonEqTk_488_; lean_object* v___x_489_; lean_object* v_body_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v_simprocDeclTk_480_ = l_Lean_Syntax_getArg(v_x_466_, v___x_479_);
v___x_481_ = lean_unsigned_to_nat(3u);
v_lparenTk_482_ = l_Lean_Syntax_getArg(v_x_466_, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(4u);
v_trigger_484_ = l_Lean_Syntax_getArg(v_x_466_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(5u);
v_rparenTk_486_ = l_Lean_Syntax_getArg(v_x_466_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(6u);
v_colonEqTk_488_ = l_Lean_Syntax_getArg(v_x_466_, v___x_487_);
v___x_489_ = lean_unsigned_to_nat(7u);
v_body_490_ = l_Lean_Syntax_getArg(v_x_466_, v___x_489_);
lean_dec(v_x_466_);
v___x_491_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocDecl___closed__0));
v___x_492_ = lean_box(0);
v___x_493_ = l_Lean_Fmt_fmtSimprocLike(v_docComment_x3f_470_, v___x_491_, v_simprocDeclTk_480_, v___x_492_, v___x_492_, v___x_492_, v___x_492_, v_declId_474_, v_lparenTk_482_, v_trigger_484_, v_rparenTk_486_, v_colonEqTk_488_, v_body_490_, v___y_471_, v___y_472_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocDecl___boxed(lean_object* v_x_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Fmt_fmtSimprocDecl(v_x_512_, v_a_513_, v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1(){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_522_ = l_Lean_Fmt_fmtAttribute;
v___x_523_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocDecl___closed__2));
v___x_524_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___closed__1));
v___x_525_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimprocDecl___boxed), 3, 0);
v___x_526_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_522_, v___x_523_, v___x_524_, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1___boxed(lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1();
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimprocDecl(lean_object* v_x_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_docComment_x3f_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_Fmt_fmtDSimprocDecl___closed__1));
lean_inc(v_x_534_);
v___x_563_ = l_Lean_Syntax_isOfKind(v_x_534_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_x_534_);
v___x_564_ = l_Lean_Fmt_Error_partialFormatter;
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v_a_536_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = l_Lean_Syntax_getArg(v_x_534_, v___x_566_);
v___x_568_ = l_Lean_Syntax_isNone(v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_567_);
v___x_570_ = l_Lean_Syntax_matchesNull(v___x_567_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_567_);
lean_dec(v_x_534_);
v___x_571_ = l_Lean_Fmt_Error_partialFormatter;
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_a_536_);
return v___x_572_;
}
else
{
lean_object* v_docComment_x3f_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_docComment_x3f_573_ = l_Lean_Syntax_getArg(v___x_567_, v___x_566_);
lean_dec(v___x_567_);
v___x_574_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__11));
lean_inc(v_docComment_x3f_573_);
v___x_575_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_docComment_x3f_573_);
lean_dec(v_x_534_);
v___x_576_ = l_Lean_Fmt_Error_partialFormatter;
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_a_536_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_docComment_x3f_573_);
v_docComment_x3f_538_ = v___x_578_;
v___y_539_ = v_a_535_;
v___y_540_ = v_a_536_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v___x_567_);
v___x_579_ = lean_box(0);
v_docComment_x3f_538_ = v___x_579_;
v___y_539_ = v_a_535_;
v___y_540_ = v_a_536_;
goto v___jp_537_;
}
}
v___jp_537_:
{
lean_object* v___x_541_; lean_object* v_declId_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_541_ = lean_unsigned_to_nat(2u);
v_declId_542_ = l_Lean_Syntax_getArg(v_x_534_, v___x_541_);
v___x_543_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_542_);
v___x_544_ = l_Lean_Syntax_isOfKind(v_declId_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_declId_542_);
lean_dec(v_docComment_x3f_538_);
lean_dec(v_x_534_);
v___x_545_ = l_Lean_Fmt_Error_partialFormatter;
v___x_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___y_540_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v_dsimprocDeclTk_548_; lean_object* v___x_549_; lean_object* v_lparenTk_550_; lean_object* v___x_551_; lean_object* v_trigger_552_; lean_object* v___x_553_; lean_object* v_rparenTk_554_; lean_object* v___x_555_; lean_object* v_colonEqTk_556_; lean_object* v___x_557_; lean_object* v_body_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v_dsimprocDeclTk_548_ = l_Lean_Syntax_getArg(v_x_534_, v___x_547_);
v___x_549_ = lean_unsigned_to_nat(3u);
v_lparenTk_550_ = l_Lean_Syntax_getArg(v_x_534_, v___x_549_);
v___x_551_ = lean_unsigned_to_nat(4u);
v_trigger_552_ = l_Lean_Syntax_getArg(v_x_534_, v___x_551_);
v___x_553_ = lean_unsigned_to_nat(5u);
v_rparenTk_554_ = l_Lean_Syntax_getArg(v_x_534_, v___x_553_);
v___x_555_ = lean_unsigned_to_nat(6u);
v_colonEqTk_556_ = l_Lean_Syntax_getArg(v_x_534_, v___x_555_);
v___x_557_ = lean_unsigned_to_nat(7u);
v_body_558_ = l_Lean_Syntax_getArg(v_x_534_, v___x_557_);
lean_dec(v_x_534_);
v___x_559_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocDecl___closed__0));
v___x_560_ = lean_box(0);
v___x_561_ = l_Lean_Fmt_fmtSimprocLike(v_docComment_x3f_538_, v___x_559_, v_dsimprocDeclTk_548_, v___x_560_, v___x_560_, v___x_560_, v___x_560_, v_declId_542_, v_lparenTk_550_, v_trigger_552_, v_rparenTk_554_, v_colonEqTk_556_, v_body_558_, v___y_539_, v___y_540_);
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDSimprocDecl___boxed(lean_object* v_x_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Fmt_fmtDSimprocDecl(v_x_580_, v_a_581_, v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1(){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_590_ = l_Lean_Fmt_fmtAttribute;
v___x_591_ = ((lean_object*)(l_Lean_Fmt_fmtDSimprocDecl___closed__1));
v___x_592_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___closed__1));
v___x_593_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDSimprocDecl___boxed), 3, 0);
v___x_594_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_590_, v___x_591_, v___x_592_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1___boxed(lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1();
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimproc(lean_object* v_x_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v_lbTk_x3f_611_; lean_object* v_ids_x3f_612_; lean_object* v_rbTk_x3f_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSimproc___closed__1));
lean_inc(v_x_602_);
v___x_647_ = l_Lean_Syntax_isOfKind(v_x_602_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_x_602_);
v___x_648_ = l_Lean_Fmt_Error_partialFormatter;
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_a_604_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v_phase_x3f_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v_docComment_x3f_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_696_ = l_Lean_Syntax_getArg(v_x_602_, v___x_650_);
v___x_697_ = l_Lean_Syntax_isNone(v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_696_);
v___x_699_ = l_Lean_Syntax_matchesNull(v___x_696_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec(v___x_696_);
lean_dec(v_x_602_);
v___x_700_ = l_Lean_Fmt_Error_partialFormatter;
v___x_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v_a_604_);
return v___x_701_;
}
else
{
lean_object* v_docComment_x3f_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_docComment_x3f_702_ = l_Lean_Syntax_getArg(v___x_696_, v___x_650_);
lean_dec(v___x_696_);
v___x_703_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__11));
lean_inc(v_docComment_x3f_702_);
v___x_704_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v_docComment_x3f_702_);
lean_dec(v_x_602_);
v___x_705_ = l_Lean_Fmt_Error_partialFormatter;
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_a_604_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v_docComment_x3f_702_);
v_docComment_x3f_676_ = v___x_707_;
v___y_677_ = v_a_603_;
v___y_678_ = v_a_604_;
goto v___jp_675_;
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v___x_696_);
v___x_708_ = lean_box(0);
v_docComment_x3f_676_ = v___x_708_;
v___y_677_ = v_a_603_;
v___y_678_ = v_a_604_;
goto v___jp_675_;
}
v___jp_651_:
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = lean_unsigned_to_nat(4u);
v___x_662_ = l_Lean_Syntax_getArg(v_x_602_, v___x_661_);
v___x_663_ = l_Lean_Syntax_isNone(v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
lean_inc(v___x_662_);
v___x_664_ = l_Lean_Syntax_matchesNull(v___x_662_, v___y_654_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v___x_662_);
lean_dec(v_phase_x3f_658_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
lean_dec(v___y_655_);
lean_dec(v_x_602_);
v___x_665_ = l_Lean_Fmt_Error_partialFormatter;
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___y_660_);
return v___x_666_;
}
else
{
lean_object* v_lbTk_x3f_667_; lean_object* v___x_668_; lean_object* v_rbTk_x3f_669_; lean_object* v_ids_x3f_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_lbTk_x3f_667_ = l_Lean_Syntax_getArg(v___x_662_, v___x_650_);
v___x_668_ = l_Lean_Syntax_getArg(v___x_662_, v___y_653_);
v_rbTk_x3f_669_ = l_Lean_Syntax_getArg(v___x_662_, v___y_652_);
lean_dec(v___x_662_);
v_ids_x3f_670_ = l_Lean_Syntax_getArgs(v___x_668_);
lean_dec(v___x_668_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v_lbTk_x3f_667_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v_ids_x3f_670_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v_rbTk_x3f_669_);
v___y_606_ = v___y_653_;
v___y_607_ = v___y_656_;
v___y_608_ = v___y_655_;
v___y_609_ = v_phase_x3f_658_;
v___y_610_ = v___y_657_;
v_lbTk_x3f_611_ = v___x_671_;
v_ids_x3f_612_ = v___x_672_;
v_rbTk_x3f_613_ = v___x_673_;
v___y_614_ = v___y_659_;
v___y_615_ = v___y_660_;
goto v___jp_605_;
}
}
else
{
lean_object* v___x_674_; 
lean_dec(v___x_662_);
v___x_674_ = lean_box(0);
v___y_606_ = v___y_653_;
v___y_607_ = v___y_656_;
v___y_608_ = v___y_655_;
v___y_609_ = v_phase_x3f_658_;
v___y_610_ = v___y_657_;
v_lbTk_x3f_611_ = v___x_674_;
v_ids_x3f_612_ = v___x_674_;
v_rbTk_x3f_613_ = v___x_674_;
v___y_614_ = v___y_659_;
v___y_615_ = v___y_660_;
goto v___jp_605_;
}
}
v___jp_675_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = l_Lean_Syntax_getArg(v_x_602_, v___x_679_);
v___x_681_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__8));
lean_inc(v___x_680_);
v___x_682_ = l_Lean_Syntax_isOfKind(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v___x_680_);
lean_dec(v_docComment_x3f_676_);
lean_dec(v_x_602_);
v___x_683_ = l_Lean_Fmt_Error_partialFormatter;
v___x_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___y_678_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v_builtinSimprocTk_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_685_ = lean_unsigned_to_nat(2u);
v_builtinSimprocTk_686_ = l_Lean_Syntax_getArg(v_x_602_, v___x_685_);
v___x_687_ = lean_unsigned_to_nat(3u);
v___x_688_ = l_Lean_Syntax_getArg(v_x_602_, v___x_687_);
v___x_689_ = l_Lean_Syntax_isNone(v___x_688_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; 
lean_inc(v___x_688_);
v___x_690_ = l_Lean_Syntax_matchesNull(v___x_688_, v___x_679_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v___x_688_);
lean_dec(v_builtinSimprocTk_686_);
lean_dec(v___x_680_);
lean_dec(v_docComment_x3f_676_);
lean_dec(v_x_602_);
v___x_691_ = l_Lean_Fmt_Error_partialFormatter;
v___x_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___y_678_);
return v___x_692_;
}
else
{
lean_object* v_phase_x3f_693_; lean_object* v___x_694_; 
v_phase_x3f_693_ = l_Lean_Syntax_getArg(v___x_688_, v___x_650_);
lean_dec(v___x_688_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v_phase_x3f_693_);
v___y_652_ = v___x_685_;
v___y_653_ = v___x_679_;
v___y_654_ = v___x_687_;
v___y_655_ = v_docComment_x3f_676_;
v___y_656_ = v_builtinSimprocTk_686_;
v___y_657_ = v___x_680_;
v_phase_x3f_658_ = v___x_694_;
v___y_659_ = v___y_677_;
v___y_660_ = v___y_678_;
goto v___jp_651_;
}
}
else
{
lean_object* v___x_695_; 
lean_dec(v___x_688_);
v___x_695_ = lean_box(0);
v___y_652_ = v___x_685_;
v___y_653_ = v___x_679_;
v___y_654_ = v___x_687_;
v___y_655_ = v_docComment_x3f_676_;
v___y_656_ = v_builtinSimprocTk_686_;
v___y_657_ = v___x_680_;
v_phase_x3f_658_ = v___x_695_;
v___y_659_ = v___y_677_;
v___y_660_ = v___y_678_;
goto v___jp_651_;
}
}
}
}
v___jp_605_:
{
lean_object* v___x_616_; lean_object* v_declId_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_616_ = lean_unsigned_to_nat(5u);
v_declId_617_ = l_Lean_Syntax_getArg(v_x_602_, v___x_616_);
v___x_618_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_617_);
v___x_619_ = l_Lean_Syntax_isOfKind(v_declId_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_declId_617_);
lean_dec(v_rbTk_x3f_613_);
lean_dec(v_ids_x3f_612_);
lean_dec(v_lbTk_x3f_611_);
lean_dec(v___y_610_);
lean_dec(v___y_609_);
lean_dec(v___y_608_);
lean_dec(v___y_607_);
lean_dec(v_x_602_);
v___x_620_ = l_Lean_Fmt_Error_partialFormatter;
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___y_615_);
return v___x_621_;
}
else
{
lean_object* v___x_622_; lean_object* v_lparenTk_623_; lean_object* v___x_624_; lean_object* v_trigger_625_; lean_object* v___x_626_; lean_object* v_rparenTk_627_; lean_object* v___x_628_; lean_object* v_colonEqTk_629_; lean_object* v___x_630_; lean_object* v_body_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_622_ = lean_unsigned_to_nat(6u);
v_lparenTk_623_ = l_Lean_Syntax_getArg(v_x_602_, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(7u);
v_trigger_625_ = l_Lean_Syntax_getArg(v_x_602_, v___x_624_);
v___x_626_ = lean_unsigned_to_nat(8u);
v_rparenTk_627_ = l_Lean_Syntax_getArg(v_x_602_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(9u);
v_colonEqTk_629_ = l_Lean_Syntax_getArg(v_x_602_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(10u);
v_body_631_ = l_Lean_Syntax_getArg(v_x_602_, v___x_630_);
lean_dec(v_x_602_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___y_610_);
v___x_633_ = lean_mk_empty_array_with_capacity(v___y_606_);
v___x_634_ = lean_array_push(v___x_633_, v___x_632_);
if (lean_obj_tag(v___y_609_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_box(0);
v___x_636_ = l_Lean_Fmt_fmtSimprocLike(v___y_608_, v___x_634_, v___y_607_, v___x_635_, v_lbTk_x3f_611_, v_ids_x3f_612_, v_rbTk_x3f_613_, v_declId_617_, v_lparenTk_623_, v_trigger_625_, v_rparenTk_627_, v_colonEqTk_629_, v_body_631_, v___y_614_, v___y_615_);
lean_dec_ref(v___x_634_);
return v___x_636_;
}
else
{
lean_object* v_val_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_val_637_ = lean_ctor_get(v___y_609_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___y_609_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v___y_609_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_val_637_);
lean_dec(v___y_609_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_val_637_);
v___x_642_ = v_reuseFailAlloc_644_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Fmt_fmtSimprocLike(v___y_608_, v___x_634_, v___y_607_, v___x_642_, v_lbTk_x3f_611_, v_ids_x3f_612_, v_rbTk_x3f_613_, v_declId_617_, v_lparenTk_623_, v_trigger_625_, v_rparenTk_627_, v_colonEqTk_629_, v_body_631_, v___y_614_, v___y_615_);
lean_dec_ref(v___x_634_);
return v___x_643_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimproc___boxed(lean_object* v_x_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Fmt_fmtBuiltinSimproc(v_x_709_, v_a_710_, v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1(){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_719_ = l_Lean_Fmt_fmtAttribute;
v___x_720_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSimproc___closed__1));
v___x_721_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___closed__1));
v___x_722_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinSimproc___boxed), 3, 0);
v___x_723_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_719_, v___x_720_, v___x_721_, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1___boxed(lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1();
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinDSimproc(lean_object* v_x_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v_lbTk_x3f_740_; lean_object* v_ids_x3f_741_; lean_object* v_rbTk_x3f_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinDSimproc___closed__1));
lean_inc(v_x_731_);
v___x_776_ = l_Lean_Syntax_isOfKind(v_x_731_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec(v_x_731_);
v___x_777_ = l_Lean_Fmt_Error_partialFormatter;
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v_a_733_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v_phase_x3f_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v_docComment_x3f_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_825_ = l_Lean_Syntax_getArg(v_x_731_, v___x_779_);
v___x_826_ = l_Lean_Syntax_isNone(v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_825_);
v___x_828_ = l_Lean_Syntax_matchesNull(v___x_825_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v___x_825_);
lean_dec(v_x_731_);
v___x_829_ = l_Lean_Fmt_Error_partialFormatter;
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v_a_733_);
return v___x_830_;
}
else
{
lean_object* v_docComment_x3f_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_docComment_x3f_831_ = l_Lean_Syntax_getArg(v___x_825_, v___x_779_);
lean_dec(v___x_825_);
v___x_832_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__11));
lean_inc(v_docComment_x3f_831_);
v___x_833_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_831_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v_docComment_x3f_831_);
lean_dec(v_x_731_);
v___x_834_ = l_Lean_Fmt_Error_partialFormatter;
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_a_733_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v_docComment_x3f_831_);
v_docComment_x3f_805_ = v___x_836_;
v___y_806_ = v_a_732_;
v___y_807_ = v_a_733_;
goto v___jp_804_;
}
}
}
else
{
lean_object* v___x_837_; 
lean_dec(v___x_825_);
v___x_837_ = lean_box(0);
v_docComment_x3f_805_ = v___x_837_;
v___y_806_ = v_a_732_;
v___y_807_ = v_a_733_;
goto v___jp_804_;
}
v___jp_780_:
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = lean_unsigned_to_nat(4u);
v___x_791_ = l_Lean_Syntax_getArg(v_x_731_, v___x_790_);
v___x_792_ = l_Lean_Syntax_isNone(v___x_791_);
if (v___x_792_ == 0)
{
uint8_t v___x_793_; 
lean_inc(v___x_791_);
v___x_793_ = l_Lean_Syntax_matchesNull(v___x_791_, v___y_782_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v___x_791_);
lean_dec(v_phase_x3f_787_);
lean_dec(v___y_786_);
lean_dec(v___y_784_);
lean_dec(v___y_781_);
lean_dec(v_x_731_);
v___x_794_ = l_Lean_Fmt_Error_partialFormatter;
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___y_789_);
return v___x_795_;
}
else
{
lean_object* v_lbTk_x3f_796_; lean_object* v___x_797_; lean_object* v_rbTk_x3f_798_; lean_object* v_ids_x3f_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_lbTk_x3f_796_ = l_Lean_Syntax_getArg(v___x_791_, v___x_779_);
v___x_797_ = l_Lean_Syntax_getArg(v___x_791_, v___y_785_);
v_rbTk_x3f_798_ = l_Lean_Syntax_getArg(v___x_791_, v___y_783_);
lean_dec(v___x_791_);
v_ids_x3f_799_ = l_Lean_Syntax_getArgs(v___x_797_);
lean_dec(v___x_797_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v_lbTk_x3f_796_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v_ids_x3f_799_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v_rbTk_x3f_798_);
v___y_735_ = v___y_781_;
v___y_736_ = v_phase_x3f_787_;
v___y_737_ = v___y_784_;
v___y_738_ = v___y_785_;
v___y_739_ = v___y_786_;
v_lbTk_x3f_740_ = v___x_800_;
v_ids_x3f_741_ = v___x_801_;
v_rbTk_x3f_742_ = v___x_802_;
v___y_743_ = v___y_788_;
v___y_744_ = v___y_789_;
goto v___jp_734_;
}
}
else
{
lean_object* v___x_803_; 
lean_dec(v___x_791_);
v___x_803_ = lean_box(0);
v___y_735_ = v___y_781_;
v___y_736_ = v_phase_x3f_787_;
v___y_737_ = v___y_784_;
v___y_738_ = v___y_785_;
v___y_739_ = v___y_786_;
v_lbTk_x3f_740_ = v___x_803_;
v_ids_x3f_741_ = v___x_803_;
v_rbTk_x3f_742_ = v___x_803_;
v___y_743_ = v___y_788_;
v___y_744_ = v___y_789_;
goto v___jp_734_;
}
}
v___jp_804_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = l_Lean_Syntax_getArg(v_x_731_, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__8));
lean_inc(v___x_809_);
v___x_811_ = l_Lean_Syntax_isOfKind(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec(v___x_809_);
lean_dec(v_docComment_x3f_805_);
lean_dec(v_x_731_);
v___x_812_ = l_Lean_Fmt_Error_partialFormatter;
v___x_813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___y_807_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; lean_object* v_builtinDSimprocTk_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_814_ = lean_unsigned_to_nat(2u);
v_builtinDSimprocTk_815_ = l_Lean_Syntax_getArg(v_x_731_, v___x_814_);
v___x_816_ = lean_unsigned_to_nat(3u);
v___x_817_ = l_Lean_Syntax_getArg(v_x_731_, v___x_816_);
v___x_818_ = l_Lean_Syntax_isNone(v___x_817_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
lean_inc(v___x_817_);
v___x_819_ = l_Lean_Syntax_matchesNull(v___x_817_, v___x_808_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec(v___x_817_);
lean_dec(v_builtinDSimprocTk_815_);
lean_dec(v___x_809_);
lean_dec(v_docComment_x3f_805_);
lean_dec(v_x_731_);
v___x_820_ = l_Lean_Fmt_Error_partialFormatter;
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___y_807_);
return v___x_821_;
}
else
{
lean_object* v_phase_x3f_822_; lean_object* v___x_823_; 
v_phase_x3f_822_ = l_Lean_Syntax_getArg(v___x_817_, v___x_779_);
lean_dec(v___x_817_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_phase_x3f_822_);
v___y_781_ = v_builtinDSimprocTk_815_;
v___y_782_ = v___x_816_;
v___y_783_ = v___x_814_;
v___y_784_ = v___x_809_;
v___y_785_ = v___x_808_;
v___y_786_ = v_docComment_x3f_805_;
v_phase_x3f_787_ = v___x_823_;
v___y_788_ = v___y_806_;
v___y_789_ = v___y_807_;
goto v___jp_780_;
}
}
else
{
lean_object* v___x_824_; 
lean_dec(v___x_817_);
v___x_824_ = lean_box(0);
v___y_781_ = v_builtinDSimprocTk_815_;
v___y_782_ = v___x_816_;
v___y_783_ = v___x_814_;
v___y_784_ = v___x_809_;
v___y_785_ = v___x_808_;
v___y_786_ = v_docComment_x3f_805_;
v_phase_x3f_787_ = v___x_824_;
v___y_788_ = v___y_806_;
v___y_789_ = v___y_807_;
goto v___jp_780_;
}
}
}
}
v___jp_734_:
{
lean_object* v___x_745_; lean_object* v_declId_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_745_ = lean_unsigned_to_nat(5u);
v_declId_746_ = l_Lean_Syntax_getArg(v_x_731_, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_746_);
v___x_748_ = l_Lean_Syntax_isOfKind(v_declId_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v_declId_746_);
lean_dec(v_rbTk_x3f_742_);
lean_dec(v_ids_x3f_741_);
lean_dec(v_lbTk_x3f_740_);
lean_dec(v___y_739_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
lean_dec(v___y_735_);
lean_dec(v_x_731_);
v___x_749_ = l_Lean_Fmt_Error_partialFormatter;
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___y_744_);
return v___x_750_;
}
else
{
lean_object* v___x_751_; lean_object* v_lparenTk_752_; lean_object* v___x_753_; lean_object* v_trigger_754_; lean_object* v___x_755_; lean_object* v_rparenTk_756_; lean_object* v___x_757_; lean_object* v_colonEqTk_758_; lean_object* v___x_759_; lean_object* v_body_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_751_ = lean_unsigned_to_nat(6u);
v_lparenTk_752_ = l_Lean_Syntax_getArg(v_x_731_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(7u);
v_trigger_754_ = l_Lean_Syntax_getArg(v_x_731_, v___x_753_);
v___x_755_ = lean_unsigned_to_nat(8u);
v_rparenTk_756_ = l_Lean_Syntax_getArg(v_x_731_, v___x_755_);
v___x_757_ = lean_unsigned_to_nat(9u);
v_colonEqTk_758_ = l_Lean_Syntax_getArg(v_x_731_, v___x_757_);
v___x_759_ = lean_unsigned_to_nat(10u);
v_body_760_ = l_Lean_Syntax_getArg(v_x_731_, v___x_759_);
lean_dec(v_x_731_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___y_737_);
v___x_762_ = lean_mk_empty_array_with_capacity(v___y_738_);
v___x_763_ = lean_array_push(v___x_762_, v___x_761_);
if (lean_obj_tag(v___y_736_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_box(0);
v___x_765_ = l_Lean_Fmt_fmtSimprocLike(v___y_739_, v___x_763_, v___y_735_, v___x_764_, v_lbTk_x3f_740_, v_ids_x3f_741_, v_rbTk_x3f_742_, v_declId_746_, v_lparenTk_752_, v_trigger_754_, v_rparenTk_756_, v_colonEqTk_758_, v_body_760_, v___y_743_, v___y_744_);
lean_dec_ref(v___x_763_);
return v___x_765_;
}
else
{
lean_object* v_val_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_774_; 
v_val_766_ = lean_ctor_get(v___y_736_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___y_736_);
if (v_isSharedCheck_774_ == 0)
{
v___x_768_ = v___y_736_;
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_val_766_);
lean_dec(v___y_736_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_val_766_);
v___x_771_ = v_reuseFailAlloc_773_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Fmt_fmtSimprocLike(v___y_739_, v___x_763_, v___y_735_, v___x_771_, v_lbTk_x3f_740_, v_ids_x3f_741_, v_rbTk_x3f_742_, v_declId_746_, v_lparenTk_752_, v_trigger_754_, v_rparenTk_756_, v_colonEqTk_758_, v_body_760_, v___y_743_, v___y_744_);
lean_dec_ref(v___x_763_);
return v___x_772_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinDSimproc___boxed(lean_object* v_x_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Fmt_fmtBuiltinDSimproc(v_x_838_, v_a_839_, v_a_840_);
lean_dec_ref(v_a_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1(){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_848_ = l_Lean_Fmt_fmtAttribute;
v___x_849_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinDSimproc___closed__1));
v___x_850_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___closed__1));
v___x_851_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinDSimproc___boxed), 3, 0);
v___x_852_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_848_, v___x_849_, v___x_850_, v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1___boxed(lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1();
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocDecl(lean_object* v_x_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_docComment_x3f_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1));
lean_inc(v_x_860_);
v___x_889_ = l_Lean_Syntax_isOfKind(v_x_860_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_x_860_);
v___x_890_ = l_Lean_Fmt_Error_partialFormatter;
v___x_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_a_862_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = l_Lean_Syntax_getArg(v_x_860_, v___x_892_);
v___x_894_ = l_Lean_Syntax_isNone(v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_893_);
v___x_896_ = l_Lean_Syntax_matchesNull(v___x_893_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec(v___x_893_);
lean_dec(v_x_860_);
v___x_897_ = l_Lean_Fmt_Error_partialFormatter;
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_a_862_);
return v___x_898_;
}
else
{
lean_object* v_docComment_x3f_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v_docComment_x3f_899_ = l_Lean_Syntax_getArg(v___x_893_, v___x_892_);
lean_dec(v___x_893_);
v___x_900_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__11));
lean_inc(v_docComment_x3f_899_);
v___x_901_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_899_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_docComment_x3f_899_);
lean_dec(v_x_860_);
v___x_902_ = l_Lean_Fmt_Error_partialFormatter;
v___x_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v_a_862_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v_docComment_x3f_899_);
v_docComment_x3f_864_ = v___x_904_;
v___y_865_ = v_a_861_;
v___y_866_ = v_a_862_;
goto v___jp_863_;
}
}
}
else
{
lean_object* v___x_905_; 
lean_dec(v___x_893_);
v___x_905_ = lean_box(0);
v_docComment_x3f_864_ = v___x_905_;
v___y_865_ = v_a_861_;
v___y_866_ = v_a_862_;
goto v___jp_863_;
}
}
v___jp_863_:
{
lean_object* v___x_867_; lean_object* v_declId_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_867_ = lean_unsigned_to_nat(2u);
v_declId_868_ = l_Lean_Syntax_getArg(v_x_860_, v___x_867_);
v___x_869_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_868_);
v___x_870_ = l_Lean_Syntax_isOfKind(v_declId_868_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_declId_868_);
lean_dec(v_docComment_x3f_864_);
lean_dec(v_x_860_);
v___x_871_ = l_Lean_Fmt_Error_partialFormatter;
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___y_866_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v_builtinSimprocDeclTk_874_; lean_object* v___x_875_; lean_object* v_lparenTk_876_; lean_object* v___x_877_; lean_object* v_trigger_878_; lean_object* v___x_879_; lean_object* v_rparenTk_880_; lean_object* v___x_881_; lean_object* v_colonEqTk_882_; lean_object* v___x_883_; lean_object* v_body_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_873_ = lean_unsigned_to_nat(1u);
v_builtinSimprocDeclTk_874_ = l_Lean_Syntax_getArg(v_x_860_, v___x_873_);
v___x_875_ = lean_unsigned_to_nat(3u);
v_lparenTk_876_ = l_Lean_Syntax_getArg(v_x_860_, v___x_875_);
v___x_877_ = lean_unsigned_to_nat(4u);
v_trigger_878_ = l_Lean_Syntax_getArg(v_x_860_, v___x_877_);
v___x_879_ = lean_unsigned_to_nat(5u);
v_rparenTk_880_ = l_Lean_Syntax_getArg(v_x_860_, v___x_879_);
v___x_881_ = lean_unsigned_to_nat(6u);
v_colonEqTk_882_ = l_Lean_Syntax_getArg(v_x_860_, v___x_881_);
v___x_883_ = lean_unsigned_to_nat(7u);
v_body_884_ = l_Lean_Syntax_getArg(v_x_860_, v___x_883_);
lean_dec(v_x_860_);
v___x_885_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocDecl___closed__0));
v___x_886_ = lean_box(0);
v___x_887_ = l_Lean_Fmt_fmtSimprocLike(v_docComment_x3f_864_, v___x_885_, v_builtinSimprocDeclTk_874_, v___x_886_, v___x_886_, v___x_886_, v___x_886_, v_declId_868_, v_lparenTk_876_, v_trigger_878_, v_rparenTk_880_, v_colonEqTk_882_, v_body_884_, v___y_865_, v___y_866_);
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocDecl___boxed(lean_object* v_x_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Fmt_fmtBuiltinSimprocDecl(v_x_906_, v_a_907_, v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1(){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_916_ = l_Lean_Fmt_fmtAttribute;
v___x_917_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSimprocDecl___closed__1));
v___x_918_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___closed__1));
v___x_919_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinSimprocDecl___boxed), 3, 0);
v___x_920_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_916_, v___x_917_, v___x_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1___boxed(lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1();
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinDSimprocDecl(lean_object* v_x_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_docComment_x3f_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1));
lean_inc(v_x_928_);
v___x_957_ = l_Lean_Syntax_isOfKind(v_x_928_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_x_928_);
v___x_958_ = l_Lean_Fmt_Error_partialFormatter;
v___x_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v_a_930_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = l_Lean_Syntax_getArg(v_x_928_, v___x_960_);
v___x_962_ = l_Lean_Syntax_isNone(v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_961_);
v___x_964_ = l_Lean_Syntax_matchesNull(v___x_961_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v___x_961_);
lean_dec(v_x_928_);
v___x_965_ = l_Lean_Fmt_Error_partialFormatter;
v___x_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v_a_930_);
return v___x_966_;
}
else
{
lean_object* v_docComment_x3f_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_docComment_x3f_967_ = l_Lean_Syntax_getArg(v___x_961_, v___x_960_);
lean_dec(v___x_961_);
v___x_968_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__11));
lean_inc(v_docComment_x3f_967_);
v___x_969_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v_docComment_x3f_967_);
lean_dec(v_x_928_);
v___x_970_ = l_Lean_Fmt_Error_partialFormatter;
v___x_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v_a_930_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v_docComment_x3f_967_);
v_docComment_x3f_932_ = v___x_972_;
v___y_933_ = v_a_929_;
v___y_934_ = v_a_930_;
goto v___jp_931_;
}
}
}
else
{
lean_object* v___x_973_; 
lean_dec(v___x_961_);
v___x_973_ = lean_box(0);
v_docComment_x3f_932_ = v___x_973_;
v___y_933_ = v_a_929_;
v___y_934_ = v_a_930_;
goto v___jp_931_;
}
}
v___jp_931_:
{
lean_object* v___x_935_; lean_object* v_declId_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_935_ = lean_unsigned_to_nat(2u);
v_declId_936_ = l_Lean_Syntax_getArg(v_x_928_, v___x_935_);
v___x_937_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_936_);
v___x_938_ = l_Lean_Syntax_isOfKind(v_declId_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v_declId_936_);
lean_dec(v_docComment_x3f_932_);
lean_dec(v_x_928_);
v___x_939_ = l_Lean_Fmt_Error_partialFormatter;
v___x_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___y_934_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; lean_object* v_builtinDSimprocDeclTk_942_; lean_object* v___x_943_; lean_object* v_lparenTk_944_; lean_object* v___x_945_; lean_object* v_trigger_946_; lean_object* v___x_947_; lean_object* v_rparenTk_948_; lean_object* v___x_949_; lean_object* v_colonEqTk_950_; lean_object* v___x_951_; lean_object* v_body_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_941_ = lean_unsigned_to_nat(1u);
v_builtinDSimprocDeclTk_942_ = l_Lean_Syntax_getArg(v_x_928_, v___x_941_);
v___x_943_ = lean_unsigned_to_nat(3u);
v_lparenTk_944_ = l_Lean_Syntax_getArg(v_x_928_, v___x_943_);
v___x_945_ = lean_unsigned_to_nat(4u);
v_trigger_946_ = l_Lean_Syntax_getArg(v_x_928_, v___x_945_);
v___x_947_ = lean_unsigned_to_nat(5u);
v_rparenTk_948_ = l_Lean_Syntax_getArg(v_x_928_, v___x_947_);
v___x_949_ = lean_unsigned_to_nat(6u);
v_colonEqTk_950_ = l_Lean_Syntax_getArg(v_x_928_, v___x_949_);
v___x_951_ = lean_unsigned_to_nat(7u);
v_body_952_ = l_Lean_Syntax_getArg(v_x_928_, v___x_951_);
lean_dec(v_x_928_);
v___x_953_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocDecl___closed__0));
v___x_954_ = lean_box(0);
v___x_955_ = l_Lean_Fmt_fmtSimprocLike(v_docComment_x3f_932_, v___x_953_, v_builtinDSimprocDeclTk_942_, v___x_954_, v___x_954_, v___x_954_, v___x_954_, v_declId_936_, v_lparenTk_944_, v_trigger_946_, v_rparenTk_948_, v_colonEqTk_950_, v_body_952_, v___y_933_, v___y_934_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinDSimprocDecl___boxed(lean_object* v_x_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Fmt_fmtBuiltinDSimprocDecl(v_x_974_, v_a_975_, v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1(){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_984_ = l_Lean_Fmt_fmtAttribute;
v___x_985_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinDSimprocDecl___closed__1));
v___x_986_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___closed__1));
v___x_987_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinDSimprocDecl___boxed), 3, 0);
v___x_988_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_984_, v___x_985_, v___x_986_, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1___boxed(lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1();
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocPattern(lean_object* v_x_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocPattern___closed__1));
lean_inc(v_x_996_);
v___x_1000_ = l_Lean_Syntax_isOfKind(v_x_996_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec(v_x_996_);
v___x_1001_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_a_998_);
return v___x_1002_;
}
else
{
lean_object* v___x_1003_; lean_object* v_declId_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1003_ = lean_unsigned_to_nat(3u);
v_declId_1004_ = l_Lean_Syntax_getArg(v_x_996_, v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_1004_);
v___x_1006_ = l_Lean_Syntax_isOfKind(v_declId_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec(v_declId_1004_);
lean_dec(v_x_996_);
v___x_1007_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_a_998_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v_simprocPatternTk_1010_; lean_object* v___x_1011_; lean_object* v_pattern_1012_; lean_object* v___x_1013_; lean_object* v_arrowTk_1014_; lean_object* v___x_1015_; 
v___x_1009_ = lean_unsigned_to_nat(0u);
v_simprocPatternTk_1010_ = l_Lean_Syntax_getArg(v_x_996_, v___x_1009_);
v___x_1011_ = lean_unsigned_to_nat(1u);
v_pattern_1012_ = l_Lean_Syntax_getArg(v_x_996_, v___x_1011_);
v___x_1013_ = lean_unsigned_to_nat(2u);
v_arrowTk_1014_ = l_Lean_Syntax_getArg(v_x_996_, v___x_1013_);
lean_dec(v_x_996_);
v___x_1015_ = l_Lean_Fmt_fmtSimprocPatternLike(v_simprocPatternTk_1010_, v_pattern_1012_, v_arrowTk_1014_, v_declId_1004_, v_a_997_, v_a_998_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocPattern___boxed(lean_object* v_x_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_Fmt_fmtSimprocPattern(v_x_1016_, v_a_1017_, v_a_1018_);
lean_dec_ref(v_a_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1(){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1026_ = l_Lean_Fmt_fmtAttribute;
v___x_1027_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocPattern___closed__1));
v___x_1028_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___closed__1));
v___x_1029_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimprocPattern___boxed), 3, 0);
v___x_1030_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1026_, v___x_1027_, v___x_1028_, v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1___boxed(lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1();
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocPattern(lean_object* v_x_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1));
lean_inc(v_x_1038_);
v___x_1042_ = l_Lean_Syntax_isOfKind(v_x_1038_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v_x_1038_);
v___x_1043_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v_a_1040_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v_declId_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1045_ = lean_unsigned_to_nat(3u);
v_declId_1046_ = l_Lean_Syntax_getArg(v_x_1038_, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Fmt_fmtSimproc___closed__1));
lean_inc(v_declId_1046_);
v___x_1048_ = l_Lean_Syntax_isOfKind(v_declId_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec(v_declId_1046_);
lean_dec(v_x_1038_);
v___x_1049_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_a_1040_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; lean_object* v_simprocPatternTk_1052_; lean_object* v___x_1053_; lean_object* v_pattern_1054_; lean_object* v___x_1055_; lean_object* v_arrowTk_1056_; lean_object* v___x_1057_; 
v___x_1051_ = lean_unsigned_to_nat(0u);
v_simprocPatternTk_1052_ = l_Lean_Syntax_getArg(v_x_1038_, v___x_1051_);
v___x_1053_ = lean_unsigned_to_nat(1u);
v_pattern_1054_ = l_Lean_Syntax_getArg(v_x_1038_, v___x_1053_);
v___x_1055_ = lean_unsigned_to_nat(2u);
v_arrowTk_1056_ = l_Lean_Syntax_getArg(v_x_1038_, v___x_1055_);
lean_dec(v_x_1038_);
v___x_1057_ = l_Lean_Fmt_fmtSimprocPatternLike(v_simprocPatternTk_1052_, v_pattern_1054_, v_arrowTk_1056_, v_declId_1046_, v_a_1039_, v_a_1040_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocPattern___boxed(lean_object* v_x_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Fmt_fmtBuiltinSimprocPattern(v_x_1058_, v_a_1059_, v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1(){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1068_ = l_Lean_Fmt_fmtAttribute;
v___x_1069_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSimprocPattern___closed__1));
v___x_1070_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___closed__1));
v___x_1071_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinSimprocPattern___boxed), 3, 0);
v___x_1072_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1068_, v___x_1069_, v___x_1070_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1___boxed(lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1();
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocAttr(lean_object* v_x_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocAttr___closed__2));
lean_inc(v_x_1082_);
v___x_1086_ = l_Lean_Syntax_isOfKind(v_x_1082_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec(v_x_1082_);
v___x_1087_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_a_1084_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; lean_object* v_simprocTk_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v_simprocTk_1090_ = l_Lean_Syntax_getArg(v_x_1082_, v___x_1089_);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = l_Lean_Syntax_getArg(v_x_1082_, v___x_1091_);
lean_dec(v_x_1082_);
v___x_1093_ = l_Lean_Syntax_isNone(v___x_1092_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; 
lean_inc(v___x_1092_);
v___x_1094_ = l_Lean_Syntax_matchesNull(v___x_1092_, v___x_1091_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v___x_1092_);
lean_dec(v_simprocTk_1090_);
v___x_1095_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_a_1084_);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = l_Lean_Syntax_getArg(v___x_1092_, v___x_1089_);
lean_dec(v___x_1092_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
v___x_1099_ = l_Lean_Fmt_fmtSimprocAttrLike(v_simprocTk_1090_, v___x_1098_, v_a_1083_, v_a_1084_);
return v___x_1099_;
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v___x_1092_);
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Lean_Fmt_fmtSimprocAttrLike(v_simprocTk_1090_, v___x_1100_, v_a_1083_, v_a_1084_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimprocAttr___boxed(lean_object* v_x_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Fmt_fmtSimprocAttr(v_x_1102_, v_a_1103_, v_a_1104_);
lean_dec_ref(v_a_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1(){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1112_ = l_Lean_Fmt_fmtAttribute;
v___x_1113_ = ((lean_object*)(l_Lean_Fmt_fmtSimprocAttr___closed__2));
v___x_1114_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___closed__1));
v___x_1115_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimprocAttr___boxed), 3, 0);
v___x_1116_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1112_, v___x_1113_, v___x_1114_, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1___boxed(lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1();
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSevalprocAttr(lean_object* v_x_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_Lean_Fmt_fmtSevalprocAttr___closed__1));
lean_inc(v_x_1125_);
v___x_1129_ = l_Lean_Syntax_isOfKind(v_x_1125_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_x_1125_);
v___x_1130_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v_a_1127_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v_sevalprocTk_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v_sevalprocTk_1133_ = l_Lean_Syntax_getArg(v_x_1125_, v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = l_Lean_Syntax_getArg(v_x_1125_, v___x_1134_);
lean_dec(v_x_1125_);
v___x_1136_ = l_Lean_Syntax_isNone(v___x_1135_);
if (v___x_1136_ == 0)
{
uint8_t v___x_1137_; 
lean_inc(v___x_1135_);
v___x_1137_ = l_Lean_Syntax_matchesNull(v___x_1135_, v___x_1134_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v___x_1135_);
lean_dec(v_sevalprocTk_1133_);
v___x_1138_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v_a_1127_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = l_Lean_Syntax_getArg(v___x_1135_, v___x_1132_);
lean_dec(v___x_1135_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
v___x_1142_ = l_Lean_Fmt_fmtSimprocAttrLike(v_sevalprocTk_1133_, v___x_1141_, v_a_1126_, v_a_1127_);
return v___x_1142_;
}
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v___x_1135_);
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Lean_Fmt_fmtSimprocAttrLike(v_sevalprocTk_1133_, v___x_1143_, v_a_1126_, v_a_1127_);
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSevalprocAttr___boxed(lean_object* v_x_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Fmt_fmtSevalprocAttr(v_x_1145_, v_a_1146_, v_a_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1(){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1155_ = l_Lean_Fmt_fmtAttribute;
v___x_1156_ = ((lean_object*)(l_Lean_Fmt_fmtSevalprocAttr___closed__1));
v___x_1157_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___closed__1));
v___x_1158_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSevalprocAttr___boxed), 3, 0);
v___x_1159_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1155_, v___x_1156_, v___x_1157_, v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1___boxed(lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1();
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocAttr(lean_object* v_x_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1));
lean_inc(v_x_1168_);
v___x_1172_ = l_Lean_Syntax_isOfKind(v_x_1168_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v_x_1168_);
v___x_1173_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_a_1170_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; lean_object* v_builtinSimprocTk_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v_builtinSimprocTk_1176_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = l_Lean_Syntax_getArg(v_x_1168_, v___x_1177_);
lean_dec(v_x_1168_);
v___x_1179_ = l_Lean_Syntax_isNone(v___x_1178_);
if (v___x_1179_ == 0)
{
uint8_t v___x_1180_; 
lean_inc(v___x_1178_);
v___x_1180_ = l_Lean_Syntax_matchesNull(v___x_1178_, v___x_1177_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v___x_1178_);
lean_dec(v_builtinSimprocTk_1176_);
v___x_1181_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v_a_1170_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_1175_);
lean_dec(v___x_1178_);
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
v___x_1185_ = l_Lean_Fmt_fmtSimprocAttrLike(v_builtinSimprocTk_1176_, v___x_1184_, v_a_1169_, v_a_1170_);
return v___x_1185_;
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec(v___x_1178_);
v___x_1186_ = lean_box(0);
v___x_1187_ = l_Lean_Fmt_fmtSimprocAttrLike(v_builtinSimprocTk_1176_, v___x_1186_, v_a_1169_, v_a_1170_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSimprocAttr___boxed(lean_object* v_x_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Fmt_fmtBuiltinSimprocAttr(v_x_1188_, v_a_1189_, v_a_1190_);
lean_dec_ref(v_a_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1(){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1198_ = l_Lean_Fmt_fmtAttribute;
v___x_1199_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSimprocAttr___closed__1));
v___x_1200_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___closed__1));
v___x_1201_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinSimprocAttr___boxed), 3, 0);
v___x_1202_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1198_, v___x_1199_, v___x_1200_, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1___boxed(lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1();
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSevalprocAttr(lean_object* v_x_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1));
lean_inc(v_x_1211_);
v___x_1215_ = l_Lean_Syntax_isOfKind(v_x_1211_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v_x_1211_);
v___x_1216_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_a_1213_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; lean_object* v_builtinSevalprocTk_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v_builtinSevalprocTk_1219_ = l_Lean_Syntax_getArg(v_x_1211_, v___x_1218_);
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = l_Lean_Syntax_getArg(v_x_1211_, v___x_1220_);
lean_dec(v_x_1211_);
v___x_1222_ = l_Lean_Syntax_isNone(v___x_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; 
lean_inc(v___x_1221_);
v___x_1223_ = l_Lean_Syntax_matchesNull(v___x_1221_, v___x_1220_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec(v___x_1221_);
lean_dec(v_builtinSevalprocTk_1219_);
v___x_1224_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_a_1213_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = l_Lean_Syntax_getArg(v___x_1221_, v___x_1218_);
lean_dec(v___x_1221_);
v___x_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
v___x_1228_ = l_Lean_Fmt_fmtSimprocAttrLike(v_builtinSevalprocTk_1219_, v___x_1227_, v_a_1212_, v_a_1213_);
return v___x_1228_;
}
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec(v___x_1221_);
v___x_1229_ = lean_box(0);
v___x_1230_ = l_Lean_Fmt_fmtSimprocAttrLike(v_builtinSevalprocTk_1219_, v___x_1229_, v_a_1212_, v_a_1213_);
return v___x_1230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinSevalprocAttr___boxed(lean_object* v_x_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Fmt_fmtBuiltinSevalprocAttr(v_x_1231_, v_a_1232_, v_a_1233_);
lean_dec_ref(v_a_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1(){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1241_ = l_Lean_Fmt_fmtAttribute;
v___x_1242_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinSevalprocAttr___closed__1));
v___x_1243_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___closed__1));
v___x_1244_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinSevalprocAttr___boxed), 3, 0);
v___x_1245_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1241_, v___x_1242_, v___x_1243_, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1___boxed(lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1();
return v_res_1247_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimproc___regBuiltin_Lean_Fmt_fmtSimproc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimproc___regBuiltin_Lean_Fmt_fmtDSimproc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocDecl___regBuiltin_Lean_Fmt_fmtSimprocDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtDSimprocDecl___regBuiltin_Lean_Fmt_fmtDSimprocDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimproc___regBuiltin_Lean_Fmt_fmtBuiltinSimproc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimproc___regBuiltin_Lean_Fmt_fmtBuiltinDSimproc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinSimprocDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinDSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinDSimprocDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocPattern___regBuiltin_Lean_Fmt_fmtSimprocPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinSimprocPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSimprocAttr___regBuiltin_Lean_Fmt_fmtSimprocAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtSevalprocAttr___regBuiltin_Lean_Fmt_fmtSevalprocAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSimprocAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Simproc_0__Lean_Fmt_fmtBuiltinSevalprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinSevalprocAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Simproc(builtin);
}
#ifdef __cplusplus
}
#endif
