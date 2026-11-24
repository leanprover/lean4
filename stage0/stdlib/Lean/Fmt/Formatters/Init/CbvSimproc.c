// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.CbvSimproc
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Init.Simproc meta import Init.CbvSimproc import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmtSimprocPatternLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSimprocAttrLike(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSimprocLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCbvSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimproc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimproc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "command__Cbv_simproc____(_):=_"};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__4_value),LEAN_SCALAR_PTR_LITERAL(12, 189, 177, 127, 220, 246, 55, 104)}};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimproc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimproc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__7_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimproc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__9_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimproc___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__11_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__11_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__9_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimproc___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__11_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__10_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtCbvSimproc___closed__11 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimproc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtCbvSimproc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 187, 81, 181, 73, 75, 167)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___boxed(lean_object*);
static const lean_array_object l_Lean_Fmt_fmtCbvSimprocDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtCbvSimprocDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimprocDecl___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimprocDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "command_Cbv_simproc_decl_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtCbvSimprocDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimprocDecl___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocDecl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocDecl___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimprocDecl___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimprocDecl___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCbvSimprocDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 241, 23, 23, 219, 215, 248, 52)}};
static const lean_object* l_Lean_Fmt_fmtCbvSimprocDecl___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimprocDecl___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtCbvSimprocDecl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 17, 206, 196, 228, 125, 221, 81)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "command__Builtin_cbv_simproc____(_):=_"};
static const lean_object* l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 62, 116, 147, 179, 57, 251, 139)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimproc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtBuiltinCbvSimproc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 120, 139, 36, 67, 221, 228, 39)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "command_Builtin_cbv_simproc_decl_(_):=_"};
static const lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 202, 177, 39, 69, 237, 175, 236)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtBuiltinCbvSimprocDecl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 192, 26, 10, 202, 93, 192, 103)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCbvSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "cbvSimprocPattern"};
static const lean_object* l_Lean_Fmt_fmtCbvSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimprocPattern___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimprocPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimprocPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCbvSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 75, 142, 45, 135, 67, 101, 69)}};
static const lean_object* l_Lean_Fmt_fmtCbvSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimprocPattern___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocPattern___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtCbvSimprocPattern"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 7, 220, 16, 186, 54, 218, 229)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "cbvSimprocPatternBuiltin"};
static const lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 134, 28, 30, 122, 199, 7, 31)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "fmtBuiltinCbvSimprocPattern"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 66, 61, 1, 77, 221, 54, 122)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCbvSimprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Fmt_fmtCbvSimprocAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtCbvSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbvSimprocAttr"};
static const lean_object* l_Lean_Fmt_fmtCbvSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocAttr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocAttr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocAttr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtCbvSimprocAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 243, 70, 210, 214, 166, 207, 129)}};
static const lean_object* l_Lean_Fmt_fmtCbvSimprocAttr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtCbvSimprocAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 8, 210, 57, 120, 220, 161, 17)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cbvSimprocBuiltinAttr"};
static const lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCbvSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 203, 241, 108, 113, 206, 69, 37)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtBuiltinCbvSimprocAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtCbvSimproc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 20, 116, 78, 159, 179, 229, 70)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimproc(lean_object* v_x_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v___y_31_; lean_object* v___y_32_; lean_object* v___y_33_; lean_object* v___y_34_; lean_object* v___y_35_; lean_object* v___y_36_; lean_object* v___y_37_; lean_object* v___y_38_; lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___y_44_; lean_object* v___y_45_; lean_object* v___y_46_; lean_object* v___y_47_; lean_object* v_phase_x3f_48_; lean_object* v___y_49_; lean_object* v___y_50_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__5));
lean_inc(v_x_25_);
v___x_80_ = l_Lean_Syntax_isOfKind(v_x_25_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_x_25_);
v___x_81_ = l_Lean_Fmt_Error_partialFormatter;
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_27_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v_docComment_x3f_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_25_, v___x_83_);
v___x_106_ = l_Lean_Syntax_isNone(v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_105_);
v___x_108_ = l_Lean_Syntax_matchesNull(v___x_105_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v___x_105_);
lean_dec(v_x_25_);
v___x_109_ = l_Lean_Fmt_Error_partialFormatter;
v___x_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v_a_27_);
return v___x_110_;
}
else
{
lean_object* v_docComment_x3f_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_docComment_x3f_111_ = l_Lean_Syntax_getArg(v___x_105_, v___x_83_);
lean_dec(v___x_105_);
v___x_112_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__11));
lean_inc(v_docComment_x3f_111_);
v___x_113_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_docComment_x3f_111_);
lean_dec(v_x_25_);
v___x_114_ = l_Lean_Fmt_Error_partialFormatter;
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_a_27_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_docComment_x3f_111_);
v_docComment_x3f_85_ = v___x_116_;
v___y_86_ = v_a_26_;
v___y_87_ = v_a_27_;
goto v___jp_84_;
}
}
}
else
{
lean_object* v___x_117_; 
lean_dec(v___x_105_);
v___x_117_ = lean_box(0);
v_docComment_x3f_85_ = v___x_117_;
v___y_86_ = v_a_26_;
v___y_87_ = v_a_27_;
goto v___jp_84_;
}
v___jp_84_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = l_Lean_Syntax_getArg(v_x_25_, v___x_88_);
v___x_90_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__8));
lean_inc(v___x_89_);
v___x_91_ = l_Lean_Syntax_isOfKind(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v___x_89_);
lean_dec(v_docComment_x3f_85_);
lean_dec(v_x_25_);
v___x_92_ = l_Lean_Fmt_Error_partialFormatter;
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___y_87_);
return v___x_93_;
}
else
{
lean_object* v___x_94_; lean_object* v_cbvSimprocTk_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_94_ = lean_unsigned_to_nat(2u);
v_cbvSimprocTk_95_ = l_Lean_Syntax_getArg(v_x_25_, v___x_94_);
v___x_96_ = lean_unsigned_to_nat(3u);
v___x_97_ = l_Lean_Syntax_getArg(v_x_25_, v___x_96_);
v___x_98_ = l_Lean_Syntax_isNone(v___x_97_);
if (v___x_98_ == 0)
{
uint8_t v___x_99_; 
lean_inc(v___x_97_);
v___x_99_ = l_Lean_Syntax_matchesNull(v___x_97_, v___x_88_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v___x_97_);
lean_dec(v_cbvSimprocTk_95_);
lean_dec(v___x_89_);
lean_dec(v_docComment_x3f_85_);
lean_dec(v_x_25_);
v___x_100_ = l_Lean_Fmt_Error_partialFormatter;
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___y_87_);
return v___x_101_;
}
else
{
lean_object* v_phase_x3f_102_; lean_object* v___x_103_; 
v_phase_x3f_102_ = l_Lean_Syntax_getArg(v___x_97_, v___x_83_);
lean_dec(v___x_97_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_phase_x3f_102_);
v___y_44_ = v___x_89_;
v___y_45_ = v_cbvSimprocTk_95_;
v___y_46_ = v___x_88_;
v___y_47_ = v_docComment_x3f_85_;
v_phase_x3f_48_ = v___x_103_;
v___y_49_ = v___y_86_;
v___y_50_ = v___y_87_;
goto v___jp_43_;
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v___x_97_);
v___x_104_ = lean_box(0);
v___y_44_ = v___x_89_;
v___y_45_ = v_cbvSimprocTk_95_;
v___y_46_ = v___x_88_;
v___y_47_ = v_docComment_x3f_85_;
v_phase_x3f_48_ = v___x_104_;
v___y_49_ = v___y_86_;
v___y_50_ = v___y_87_;
goto v___jp_43_;
}
}
}
}
v___jp_28_:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(0);
v___x_42_ = l_Lean_Fmt_fmtSimprocLike(v___y_39_, v___y_35_, v___y_32_, v___y_40_, v___x_41_, v___x_41_, v___x_41_, v___y_33_, v___y_31_, v___y_29_, v___y_38_, v___y_37_, v___y_30_, v___y_34_, v___y_36_);
lean_dec_ref(v___y_35_);
return v___x_42_;
}
v___jp_43_:
{
lean_object* v___x_51_; lean_object* v_declId_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_51_ = lean_unsigned_to_nat(4u);
v_declId_52_ = l_Lean_Syntax_getArg(v_x_25_, v___x_51_);
v___x_53_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__1));
lean_inc(v_declId_52_);
v___x_54_ = l_Lean_Syntax_isOfKind(v_declId_52_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_declId_52_);
lean_dec(v_phase_x3f_48_);
lean_dec(v___y_47_);
lean_dec(v___y_45_);
lean_dec(v___y_44_);
lean_dec(v_x_25_);
v___x_55_ = l_Lean_Fmt_Error_partialFormatter;
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___y_50_);
return v___x_56_;
}
else
{
lean_object* v___x_57_; lean_object* v_lparenTk_58_; lean_object* v___x_59_; lean_object* v_trigger_60_; lean_object* v___x_61_; lean_object* v_rparenTk_62_; lean_object* v___x_63_; lean_object* v_colonEqTk_64_; lean_object* v___x_65_; lean_object* v_body_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_57_ = lean_unsigned_to_nat(5u);
v_lparenTk_58_ = l_Lean_Syntax_getArg(v_x_25_, v___x_57_);
v___x_59_ = lean_unsigned_to_nat(6u);
v_trigger_60_ = l_Lean_Syntax_getArg(v_x_25_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(7u);
v_rparenTk_62_ = l_Lean_Syntax_getArg(v_x_25_, v___x_61_);
v___x_63_ = lean_unsigned_to_nat(8u);
v_colonEqTk_64_ = l_Lean_Syntax_getArg(v_x_25_, v___x_63_);
v___x_65_ = lean_unsigned_to_nat(9u);
v_body_66_ = l_Lean_Syntax_getArg(v_x_25_, v___x_65_);
lean_dec(v_x_25_);
v___x_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_67_, 0, v___y_44_);
v___x_68_ = lean_mk_empty_array_with_capacity(v___y_46_);
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
if (lean_obj_tag(v_phase_x3f_48_) == 0)
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
v___y_29_ = v_trigger_60_;
v___y_30_ = v_body_66_;
v___y_31_ = v_lparenTk_58_;
v___y_32_ = v___y_45_;
v___y_33_ = v_declId_52_;
v___y_34_ = v___y_49_;
v___y_35_ = v___x_69_;
v___y_36_ = v___y_50_;
v___y_37_ = v_colonEqTk_64_;
v___y_38_ = v_rparenTk_62_;
v___y_39_ = v___y_47_;
v___y_40_ = v___x_70_;
goto v___jp_28_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
v_val_71_ = lean_ctor_get(v_phase_x3f_48_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v_phase_x3f_48_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v_phase_x3f_48_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_val_71_);
lean_dec(v_phase_x3f_48_);
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
v___y_29_ = v_trigger_60_;
v___y_30_ = v_body_66_;
v___y_31_ = v_lparenTk_58_;
v___y_32_ = v___y_45_;
v___y_33_ = v_declId_52_;
v___y_34_ = v___y_49_;
v___y_35_ = v___x_69_;
v___y_36_ = v___y_50_;
v___y_37_ = v_colonEqTk_64_;
v___y_38_ = v_rparenTk_62_;
v___y_39_ = v___y_47_;
v___y_40_ = v___x_76_;
goto v___jp_28_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimproc___boxed(lean_object* v_x_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Fmt_fmtCbvSimproc(v_x_118_, v_a_119_, v_a_120_);
lean_dec_ref(v_a_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1(){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = l_Lean_Fmt_fmtAttribute;
v___x_130_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__5));
v___x_131_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___closed__2));
v___x_132_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCbvSimproc___boxed), 3, 0);
v___x_133_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_129_, v___x_130_, v___x_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1___boxed(lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1();
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocDecl(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_docComment_x3f_147_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimprocDecl___closed__2));
lean_inc(v_x_143_);
v___x_172_ = l_Lean_Syntax_isOfKind(v_x_143_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_x_143_);
v___x_173_ = l_Lean_Fmt_Error_partialFormatter;
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_145_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = l_Lean_Syntax_getArg(v_x_143_, v___x_175_);
v___x_177_ = l_Lean_Syntax_isNone(v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_176_);
v___x_179_ = l_Lean_Syntax_matchesNull(v___x_176_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v___x_176_);
lean_dec(v_x_143_);
v___x_180_ = l_Lean_Fmt_Error_partialFormatter;
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_a_145_);
return v___x_181_;
}
else
{
lean_object* v_docComment_x3f_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_docComment_x3f_182_ = l_Lean_Syntax_getArg(v___x_176_, v___x_175_);
lean_dec(v___x_176_);
v___x_183_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__11));
lean_inc(v_docComment_x3f_182_);
v___x_184_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_docComment_x3f_182_);
lean_dec(v_x_143_);
v___x_185_ = l_Lean_Fmt_Error_partialFormatter;
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_145_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v_docComment_x3f_182_);
v_docComment_x3f_147_ = v___x_187_;
v___y_148_ = v_a_144_;
v___y_149_ = v_a_145_;
goto v___jp_146_;
}
}
}
else
{
lean_object* v___x_188_; 
lean_dec(v___x_176_);
v___x_188_ = lean_box(0);
v_docComment_x3f_147_ = v___x_188_;
v___y_148_ = v_a_144_;
v___y_149_ = v_a_145_;
goto v___jp_146_;
}
}
v___jp_146_:
{
lean_object* v___x_150_; lean_object* v_declId_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(2u);
v_declId_151_ = l_Lean_Syntax_getArg(v_x_143_, v___x_150_);
v___x_152_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__1));
lean_inc(v_declId_151_);
v___x_153_ = l_Lean_Syntax_isOfKind(v_declId_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_declId_151_);
lean_dec(v_docComment_x3f_147_);
lean_dec(v_x_143_);
v___x_154_ = l_Lean_Fmt_Error_partialFormatter;
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___y_149_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v_cbvSimprocDeclTk_157_; lean_object* v___x_158_; lean_object* v_lparenTk_159_; lean_object* v___x_160_; lean_object* v_trigger_161_; lean_object* v___x_162_; lean_object* v_rparenTk_163_; lean_object* v___x_164_; lean_object* v_colonEqTk_165_; lean_object* v___x_166_; lean_object* v_body_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v_cbvSimprocDeclTk_157_ = l_Lean_Syntax_getArg(v_x_143_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(3u);
v_lparenTk_159_ = l_Lean_Syntax_getArg(v_x_143_, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(4u);
v_trigger_161_ = l_Lean_Syntax_getArg(v_x_143_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(5u);
v_rparenTk_163_ = l_Lean_Syntax_getArg(v_x_143_, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(6u);
v_colonEqTk_165_ = l_Lean_Syntax_getArg(v_x_143_, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(7u);
v_body_167_ = l_Lean_Syntax_getArg(v_x_143_, v___x_166_);
lean_dec(v_x_143_);
v___x_168_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimprocDecl___closed__0));
v___x_169_ = lean_box(0);
v___x_170_ = l_Lean_Fmt_fmtSimprocLike(v_docComment_x3f_147_, v___x_168_, v_cbvSimprocDeclTk_157_, v___x_169_, v___x_169_, v___x_169_, v___x_169_, v_declId_151_, v_lparenTk_159_, v_trigger_161_, v_rparenTk_163_, v_colonEqTk_165_, v_body_167_, v___y_148_, v___y_149_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocDecl___boxed(lean_object* v_x_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Fmt_fmtCbvSimprocDecl(v_x_189_, v_a_190_, v_a_191_);
lean_dec_ref(v_a_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1(){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_199_ = l_Lean_Fmt_fmtAttribute;
v___x_200_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimprocDecl___closed__2));
v___x_201_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___closed__1));
v___x_202_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCbvSimprocDecl___boxed), 3, 0);
v___x_203_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_199_, v___x_200_, v___x_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1___boxed(lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1();
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimproc(lean_object* v_x_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v_phase_x3f_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1));
lean_inc(v_x_211_);
v___x_266_ = l_Lean_Syntax_isOfKind(v_x_211_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_x_211_);
v___x_267_ = l_Lean_Fmt_Error_partialFormatter;
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_213_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v_docComment_x3f_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Lean_Syntax_getArg(v_x_211_, v___x_269_);
v___x_292_ = l_Lean_Syntax_isNone(v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_291_);
v___x_294_ = l_Lean_Syntax_matchesNull(v___x_291_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v___x_291_);
lean_dec(v_x_211_);
v___x_295_ = l_Lean_Fmt_Error_partialFormatter;
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_a_213_);
return v___x_296_;
}
else
{
lean_object* v_docComment_x3f_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_docComment_x3f_297_ = l_Lean_Syntax_getArg(v___x_291_, v___x_269_);
lean_dec(v___x_291_);
v___x_298_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__11));
lean_inc(v_docComment_x3f_297_);
v___x_299_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_docComment_x3f_297_);
lean_dec(v_x_211_);
v___x_300_ = l_Lean_Fmt_Error_partialFormatter;
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_a_213_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v_docComment_x3f_297_);
v_docComment_x3f_271_ = v___x_302_;
v___y_272_ = v_a_212_;
v___y_273_ = v_a_213_;
goto v___jp_270_;
}
}
}
else
{
lean_object* v___x_303_; 
lean_dec(v___x_291_);
v___x_303_ = lean_box(0);
v_docComment_x3f_271_ = v___x_303_;
v___y_272_ = v_a_212_;
v___y_273_ = v_a_213_;
goto v___jp_270_;
}
v___jp_270_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = l_Lean_Syntax_getArg(v_x_211_, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__8));
lean_inc(v___x_275_);
v___x_277_ = l_Lean_Syntax_isOfKind(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v___x_275_);
lean_dec(v_docComment_x3f_271_);
lean_dec(v_x_211_);
v___x_278_ = l_Lean_Fmt_Error_partialFormatter;
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___y_273_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v_builtinCbvSimprocTk_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_280_ = lean_unsigned_to_nat(2u);
v_builtinCbvSimprocTk_281_ = l_Lean_Syntax_getArg(v_x_211_, v___x_280_);
v___x_282_ = lean_unsigned_to_nat(3u);
v___x_283_ = l_Lean_Syntax_getArg(v_x_211_, v___x_282_);
v___x_284_ = l_Lean_Syntax_isNone(v___x_283_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
lean_inc(v___x_283_);
v___x_285_ = l_Lean_Syntax_matchesNull(v___x_283_, v___x_274_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v___x_283_);
lean_dec(v_builtinCbvSimprocTk_281_);
lean_dec(v___x_275_);
lean_dec(v_docComment_x3f_271_);
lean_dec(v_x_211_);
v___x_286_ = l_Lean_Fmt_Error_partialFormatter;
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___y_273_);
return v___x_287_;
}
else
{
lean_object* v_phase_x3f_288_; lean_object* v___x_289_; 
v_phase_x3f_288_ = l_Lean_Syntax_getArg(v___x_283_, v___x_269_);
lean_dec(v___x_283_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_phase_x3f_288_);
v___y_230_ = v_builtinCbvSimprocTk_281_;
v___y_231_ = v___x_274_;
v___y_232_ = v___x_275_;
v___y_233_ = v_docComment_x3f_271_;
v_phase_x3f_234_ = v___x_289_;
v___y_235_ = v___y_272_;
v___y_236_ = v___y_273_;
goto v___jp_229_;
}
}
else
{
lean_object* v___x_290_; 
lean_dec(v___x_283_);
v___x_290_ = lean_box(0);
v___y_230_ = v_builtinCbvSimprocTk_281_;
v___y_231_ = v___x_274_;
v___y_232_ = v___x_275_;
v___y_233_ = v_docComment_x3f_271_;
v_phase_x3f_234_ = v___x_290_;
v___y_235_ = v___y_272_;
v___y_236_ = v___y_273_;
goto v___jp_229_;
}
}
}
}
v___jp_214_:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_box(0);
v___x_228_ = l_Lean_Fmt_fmtSimprocLike(v___y_223_, v___y_218_, v___y_217_, v___y_226_, v___x_227_, v___x_227_, v___x_227_, v___y_216_, v___y_221_, v___y_219_, v___y_222_, v___y_225_, v___y_224_, v___y_220_, v___y_215_);
lean_dec_ref(v___y_218_);
return v___x_228_;
}
v___jp_229_:
{
lean_object* v___x_237_; lean_object* v_declId_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_237_ = lean_unsigned_to_nat(4u);
v_declId_238_ = l_Lean_Syntax_getArg(v_x_211_, v___x_237_);
v___x_239_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__1));
lean_inc(v_declId_238_);
v___x_240_ = l_Lean_Syntax_isOfKind(v_declId_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v_declId_238_);
lean_dec(v_phase_x3f_234_);
lean_dec(v___y_233_);
lean_dec(v___y_232_);
lean_dec(v___y_230_);
lean_dec(v_x_211_);
v___x_241_ = l_Lean_Fmt_Error_partialFormatter;
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___y_236_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v_lparenTk_244_; lean_object* v___x_245_; lean_object* v_trigger_246_; lean_object* v___x_247_; lean_object* v_rparenTk_248_; lean_object* v___x_249_; lean_object* v_colonEqTk_250_; lean_object* v___x_251_; lean_object* v_body_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_243_ = lean_unsigned_to_nat(5u);
v_lparenTk_244_ = l_Lean_Syntax_getArg(v_x_211_, v___x_243_);
v___x_245_ = lean_unsigned_to_nat(6u);
v_trigger_246_ = l_Lean_Syntax_getArg(v_x_211_, v___x_245_);
v___x_247_ = lean_unsigned_to_nat(7u);
v_rparenTk_248_ = l_Lean_Syntax_getArg(v_x_211_, v___x_247_);
v___x_249_ = lean_unsigned_to_nat(8u);
v_colonEqTk_250_ = l_Lean_Syntax_getArg(v_x_211_, v___x_249_);
v___x_251_ = lean_unsigned_to_nat(9u);
v_body_252_ = l_Lean_Syntax_getArg(v_x_211_, v___x_251_);
lean_dec(v_x_211_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v___y_232_);
v___x_254_ = lean_mk_empty_array_with_capacity(v___y_231_);
v___x_255_ = lean_array_push(v___x_254_, v___x_253_);
if (lean_obj_tag(v_phase_x3f_234_) == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_box(0);
v___y_215_ = v___y_236_;
v___y_216_ = v_declId_238_;
v___y_217_ = v___y_230_;
v___y_218_ = v___x_255_;
v___y_219_ = v_trigger_246_;
v___y_220_ = v___y_235_;
v___y_221_ = v_lparenTk_244_;
v___y_222_ = v_rparenTk_248_;
v___y_223_ = v___y_233_;
v___y_224_ = v_body_252_;
v___y_225_ = v_colonEqTk_250_;
v___y_226_ = v___x_256_;
goto v___jp_214_;
}
else
{
lean_object* v_val_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_val_257_ = lean_ctor_get(v_phase_x3f_234_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v_phase_x3f_234_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v_phase_x3f_234_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_val_257_);
lean_dec(v_phase_x3f_234_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_val_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
v___y_215_ = v___y_236_;
v___y_216_ = v_declId_238_;
v___y_217_ = v___y_230_;
v___y_218_ = v___x_255_;
v___y_219_ = v_trigger_246_;
v___y_220_ = v___y_235_;
v___y_221_ = v_lparenTk_244_;
v___y_222_ = v_rparenTk_248_;
v___y_223_ = v___y_233_;
v___y_224_ = v_body_252_;
v___y_225_ = v_colonEqTk_250_;
v___y_226_ = v___x_262_;
goto v___jp_214_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimproc___boxed(lean_object* v_x_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Fmt_fmtBuiltinCbvSimproc(v_x_304_, v_a_305_, v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1(){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_314_ = l_Lean_Fmt_fmtAttribute;
v___x_315_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCbvSimproc___closed__1));
v___x_316_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___closed__1));
v___x_317_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinCbvSimproc___boxed), 3, 0);
v___x_318_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_314_, v___x_315_, v___x_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1___boxed(lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1();
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocDecl(lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_docComment_x3f_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1));
lean_inc(v_x_326_);
v___x_355_ = l_Lean_Syntax_isOfKind(v_x_326_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v_x_326_);
v___x_356_ = l_Lean_Fmt_Error_partialFormatter;
v___x_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_a_328_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = l_Lean_Syntax_getArg(v_x_326_, v___x_358_);
v___x_360_ = l_Lean_Syntax_isNone(v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_359_);
v___x_362_ = l_Lean_Syntax_matchesNull(v___x_359_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v___x_359_);
lean_dec(v_x_326_);
v___x_363_ = l_Lean_Fmt_Error_partialFormatter;
v___x_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_a_328_);
return v___x_364_;
}
else
{
lean_object* v_docComment_x3f_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_docComment_x3f_365_ = l_Lean_Syntax_getArg(v___x_359_, v___x_358_);
lean_dec(v___x_359_);
v___x_366_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__11));
lean_inc(v_docComment_x3f_365_);
v___x_367_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_docComment_x3f_365_);
lean_dec(v_x_326_);
v___x_368_ = l_Lean_Fmt_Error_partialFormatter;
v___x_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_a_328_);
return v___x_369_;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_docComment_x3f_365_);
v_docComment_x3f_330_ = v___x_370_;
v___y_331_ = v_a_327_;
v___y_332_ = v_a_328_;
goto v___jp_329_;
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v___x_359_);
v___x_371_ = lean_box(0);
v_docComment_x3f_330_ = v___x_371_;
v___y_331_ = v_a_327_;
v___y_332_ = v_a_328_;
goto v___jp_329_;
}
}
v___jp_329_:
{
lean_object* v___x_333_; lean_object* v_declId_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_333_ = lean_unsigned_to_nat(2u);
v_declId_334_ = l_Lean_Syntax_getArg(v_x_326_, v___x_333_);
v___x_335_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__1));
lean_inc(v_declId_334_);
v___x_336_ = l_Lean_Syntax_isOfKind(v_declId_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_declId_334_);
lean_dec(v_docComment_x3f_330_);
lean_dec(v_x_326_);
v___x_337_ = l_Lean_Fmt_Error_partialFormatter;
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___y_332_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v_builtinCbvSimprocDeclTk_340_; lean_object* v___x_341_; lean_object* v_lparenTk_342_; lean_object* v___x_343_; lean_object* v_trigger_344_; lean_object* v___x_345_; lean_object* v_rparenTk_346_; lean_object* v___x_347_; lean_object* v_colonEqTk_348_; lean_object* v___x_349_; lean_object* v_body_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v_builtinCbvSimprocDeclTk_340_ = l_Lean_Syntax_getArg(v_x_326_, v___x_339_);
v___x_341_ = lean_unsigned_to_nat(3u);
v_lparenTk_342_ = l_Lean_Syntax_getArg(v_x_326_, v___x_341_);
v___x_343_ = lean_unsigned_to_nat(4u);
v_trigger_344_ = l_Lean_Syntax_getArg(v_x_326_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(5u);
v_rparenTk_346_ = l_Lean_Syntax_getArg(v_x_326_, v___x_345_);
v___x_347_ = lean_unsigned_to_nat(6u);
v_colonEqTk_348_ = l_Lean_Syntax_getArg(v_x_326_, v___x_347_);
v___x_349_ = lean_unsigned_to_nat(7u);
v_body_350_ = l_Lean_Syntax_getArg(v_x_326_, v___x_349_);
lean_dec(v_x_326_);
v___x_351_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimprocDecl___closed__0));
v___x_352_ = lean_box(0);
v___x_353_ = l_Lean_Fmt_fmtSimprocLike(v_docComment_x3f_330_, v___x_351_, v_builtinCbvSimprocDeclTk_340_, v___x_352_, v___x_352_, v___x_352_, v___x_352_, v_declId_334_, v_lparenTk_342_, v_trigger_344_, v_rparenTk_346_, v_colonEqTk_348_, v_body_350_, v___y_331_, v___y_332_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___boxed(lean_object* v_x_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Fmt_fmtBuiltinCbvSimprocDecl(v_x_372_, v_a_373_, v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1(){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_382_ = l_Lean_Fmt_fmtAttribute;
v___x_383_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___closed__1));
v___x_384_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___closed__1));
v___x_385_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinCbvSimprocDecl___boxed), 3, 0);
v___x_386_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_382_, v___x_383_, v___x_384_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1___boxed(lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1();
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocPattern(lean_object* v_x_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimprocPattern___closed__1));
lean_inc(v_x_394_);
v___x_398_ = l_Lean_Syntax_isOfKind(v_x_394_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v_x_394_);
v___x_399_ = l_Lean_Fmt_Error_partialFormatter;
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v_a_396_);
return v___x_400_;
}
else
{
lean_object* v___x_401_; lean_object* v_declId_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_401_ = lean_unsigned_to_nat(3u);
v_declId_402_ = l_Lean_Syntax_getArg(v_x_394_, v___x_401_);
v___x_403_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__1));
lean_inc(v_declId_402_);
v___x_404_ = l_Lean_Syntax_isOfKind(v_declId_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_declId_402_);
lean_dec(v_x_394_);
v___x_405_ = l_Lean_Fmt_Error_partialFormatter;
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_a_396_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v_cbvSimprocPatternTk_408_; lean_object* v___x_409_; lean_object* v_pattern_410_; lean_object* v___x_411_; lean_object* v_arrowTk_412_; lean_object* v___x_413_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v_cbvSimprocPatternTk_408_ = l_Lean_Syntax_getArg(v_x_394_, v___x_407_);
v___x_409_ = lean_unsigned_to_nat(1u);
v_pattern_410_ = l_Lean_Syntax_getArg(v_x_394_, v___x_409_);
v___x_411_ = lean_unsigned_to_nat(2u);
v_arrowTk_412_ = l_Lean_Syntax_getArg(v_x_394_, v___x_411_);
lean_dec(v_x_394_);
v___x_413_ = l_Lean_Fmt_fmtSimprocPatternLike(v_cbvSimprocPatternTk_408_, v_pattern_410_, v_arrowTk_412_, v_declId_402_, v_a_395_, v_a_396_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocPattern___boxed(lean_object* v_x_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Fmt_fmtCbvSimprocPattern(v_x_414_, v_a_415_, v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1(){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_424_ = l_Lean_Fmt_fmtAttribute;
v___x_425_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimprocPattern___closed__1));
v___x_426_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___closed__1));
v___x_427_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCbvSimprocPattern___boxed), 3, 0);
v___x_428_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_424_, v___x_425_, v___x_426_, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1___boxed(lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1();
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocPattern(lean_object* v_x_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1));
lean_inc(v_x_436_);
v___x_440_ = l_Lean_Syntax_isOfKind(v_x_436_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v_x_436_);
v___x_441_ = l_Lean_Fmt_Error_partialFormatter;
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v_a_438_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v_declId_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(3u);
v_declId_444_ = l_Lean_Syntax_getArg(v_x_436_, v___x_443_);
v___x_445_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimproc___closed__1));
lean_inc(v_declId_444_);
v___x_446_ = l_Lean_Syntax_isOfKind(v_declId_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_declId_444_);
lean_dec(v_x_436_);
v___x_447_ = l_Lean_Fmt_Error_partialFormatter;
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_a_438_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; lean_object* v_cbvSimprocPatternTk_450_; lean_object* v___x_451_; lean_object* v_pattern_452_; lean_object* v___x_453_; lean_object* v_arrowTk_454_; lean_object* v___x_455_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v_cbvSimprocPatternTk_450_ = l_Lean_Syntax_getArg(v_x_436_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(1u);
v_pattern_452_ = l_Lean_Syntax_getArg(v_x_436_, v___x_451_);
v___x_453_ = lean_unsigned_to_nat(2u);
v_arrowTk_454_ = l_Lean_Syntax_getArg(v_x_436_, v___x_453_);
lean_dec(v_x_436_);
v___x_455_ = l_Lean_Fmt_fmtSimprocPatternLike(v_cbvSimprocPatternTk_450_, v_pattern_452_, v_arrowTk_454_, v_declId_444_, v_a_437_, v_a_438_);
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___boxed(lean_object* v_x_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Fmt_fmtBuiltinCbvSimprocPattern(v_x_456_, v_a_457_, v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1(){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_466_ = l_Lean_Fmt_fmtAttribute;
v___x_467_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___closed__1));
v___x_468_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___closed__1));
v___x_469_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinCbvSimprocPattern___boxed), 3, 0);
v___x_470_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_466_, v___x_467_, v___x_468_, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1___boxed(lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1();
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocAttr(lean_object* v_x_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimprocAttr___closed__2));
lean_inc(v_x_480_);
v___x_484_ = l_Lean_Syntax_isOfKind(v_x_480_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_x_480_);
v___x_485_ = l_Lean_Fmt_Error_partialFormatter;
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_a_482_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v_cbvSimprocTk_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_487_ = lean_unsigned_to_nat(0u);
v_cbvSimprocTk_488_ = l_Lean_Syntax_getArg(v_x_480_, v___x_487_);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = l_Lean_Syntax_getArg(v_x_480_, v___x_489_);
lean_dec(v_x_480_);
v___x_491_ = l_Lean_Syntax_isNone(v___x_490_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
lean_inc(v___x_490_);
v___x_492_ = l_Lean_Syntax_matchesNull(v___x_490_, v___x_489_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v___x_490_);
lean_dec(v_cbvSimprocTk_488_);
v___x_493_ = l_Lean_Fmt_Error_partialFormatter;
v___x_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v_a_482_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = l_Lean_Syntax_getArg(v___x_490_, v___x_487_);
lean_dec(v___x_490_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
v___x_497_ = l_Lean_Fmt_fmtSimprocAttrLike(v_cbvSimprocTk_488_, v___x_496_, v_a_481_, v_a_482_);
return v___x_497_;
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v___x_490_);
v___x_498_ = lean_box(0);
v___x_499_ = l_Lean_Fmt_fmtSimprocAttrLike(v_cbvSimprocTk_488_, v___x_498_, v_a_481_, v_a_482_);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCbvSimprocAttr___boxed(lean_object* v_x_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Fmt_fmtCbvSimprocAttr(v_x_500_, v_a_501_, v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1(){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_510_ = l_Lean_Fmt_fmtAttribute;
v___x_511_ = ((lean_object*)(l_Lean_Fmt_fmtCbvSimprocAttr___closed__2));
v___x_512_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___closed__1));
v___x_513_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCbvSimprocAttr___boxed), 3, 0);
v___x_514_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_510_, v___x_511_, v___x_512_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1___boxed(lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1();
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocAttr(lean_object* v_x_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1));
lean_inc(v_x_523_);
v___x_527_ = l_Lean_Syntax_isOfKind(v_x_523_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_x_523_);
v___x_528_ = l_Lean_Fmt_Error_partialFormatter;
v___x_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_a_525_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; lean_object* v_builtinCbvSimprocTk_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_530_ = lean_unsigned_to_nat(0u);
v_builtinCbvSimprocTk_531_ = l_Lean_Syntax_getArg(v_x_523_, v___x_530_);
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = l_Lean_Syntax_getArg(v_x_523_, v___x_532_);
lean_dec(v_x_523_);
v___x_534_ = l_Lean_Syntax_isNone(v___x_533_);
if (v___x_534_ == 0)
{
uint8_t v___x_535_; 
lean_inc(v___x_533_);
v___x_535_ = l_Lean_Syntax_matchesNull(v___x_533_, v___x_532_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v___x_533_);
lean_dec(v_builtinCbvSimprocTk_531_);
v___x_536_ = l_Lean_Fmt_Error_partialFormatter;
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_a_525_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_Syntax_getArg(v___x_533_, v___x_530_);
lean_dec(v___x_533_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
v___x_540_ = l_Lean_Fmt_fmtSimprocAttrLike(v_builtinCbvSimprocTk_531_, v___x_539_, v_a_524_, v_a_525_);
return v___x_540_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v___x_533_);
v___x_541_ = lean_box(0);
v___x_542_ = l_Lean_Fmt_fmtSimprocAttrLike(v_builtinCbvSimprocTk_531_, v___x_541_, v_a_524_, v_a_525_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___boxed(lean_object* v_x_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Fmt_fmtBuiltinCbvSimprocAttr(v_x_543_, v_a_544_, v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1(){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_553_ = l_Lean_Fmt_fmtAttribute;
v___x_554_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___closed__1));
v___x_555_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___closed__1));
v___x_556_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinCbvSimprocAttr___boxed), 3, 0);
v___x_557_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_553_, v___x_554_, v___x_555_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1___boxed(lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1();
return v_res_559_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_CbvSimproc(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimproc___regBuiltin_Lean_Fmt_fmtCbvSimproc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtCbvSimprocDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimproc___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimproc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocDecl___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtCbvSimprocPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocPattern___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtCbvSimprocAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_CbvSimproc_0__Lean_Fmt_fmtBuiltinCbvSimprocAttr___regBuiltin_Lean_Fmt_fmtBuiltinCbvSimprocAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_CbvSimproc(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Simproc(uint8_t builtin);
lean_object* initialize_Init_CbvSimproc(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_CbvSimproc(builtin);
}
#ifdef __cplusplus
}
#endif
