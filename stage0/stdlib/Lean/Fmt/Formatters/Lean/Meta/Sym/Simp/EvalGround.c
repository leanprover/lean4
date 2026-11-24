// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Meta.Sym.Simp.EvalGround
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Meta.Sym.Simp.EvalGround import Init.Data
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "commandDeclare_eval_bin__"};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__4_value),LEAN_SCALAR_PTR_LITERAL(165, 42, 106, 143, 34, 177, 253, 246)}};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtSimpDeclareEvalBin"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 133, 117, 21, 108, 54, 154, 29)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "commandDeclare_eval_bin_bitwise__"};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 104, 121, 56, 9, 239, 32, 71)}};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "fmtSimpDeclareEvalBinBitwise"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 196, 0, 236, 140, 53, 148, 54)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "commandDeclare_eval_bin_bool_pred__"};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 0, 79, 120, 103, 246, 194, 21)}};
static const lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "fmtSimpDeclareEvalBinBoolPred"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 159, 218, 73, 217, 214, 42, 141)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin(lean_object* v_x_15_, lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5));
lean_inc(v_x_15_);
v___x_19_ = l_Lean_Syntax_isOfKind(v_x_15_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_x_15_);
v___x_20_ = l_Lean_Fmt_Error_partialFormatter;
v___x_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v_a_17_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = l_Lean_Syntax_getArg(v_x_15_, v___x_22_);
v___x_24_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__7));
lean_inc(v___x_23_);
v___x_25_ = l_Lean_Syntax_isOfKind(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v___x_23_);
lean_dec(v_x_15_);
v___x_26_ = l_Lean_Fmt_Error_partialFormatter;
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v_a_17_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v_declareTk_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v_declareTk_29_ = l_Lean_Syntax_getArg(v_x_15_, v___x_28_);
v___x_30_ = l_Lean_Fmt_fmt(v_declareTk_29_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v_a_32_; lean_object* v___x_33_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_31_);
v_a_32_ = lean_ctor_get(v___x_30_, 1);
lean_inc(v_a_32_);
lean_dec_ref_known(v___x_30_, 2);
v___x_33_ = l_Lean_Fmt_fmt(v___x_23_, v_a_16_, v_a_32_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v_a_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_a_34_);
v_a_35_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_a_35_);
lean_dec_ref_known(v___x_33_, 2);
v___x_36_ = lean_unsigned_to_nat(2u);
v___x_37_ = l_Lean_Syntax_getArg(v_x_15_, v___x_36_);
lean_dec(v_x_15_);
v___x_38_ = l_Lean_Fmt_fmt(v___x_37_, v_a_16_, v_a_35_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_55_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_a_40_ = lean_ctor_get(v___x_38_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_55_ == 0)
{
v___x_42_ = v___x_38_;
v_isShared_43_ = v_isSharedCheck_55_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_55_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_44_ = lean_unsigned_to_nat(3u);
v___x_45_ = lean_mk_empty_array_with_capacity(v___x_44_);
v___x_46_ = lean_array_push(v___x_45_, v_a_31_);
v___x_47_ = lean_array_push(v___x_46_, v_a_34_);
v___x_48_ = lean_array_push(v___x_47_, v_a_39_);
v___x_49_ = 0;
v___x_50_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_50_, 0, v___x_25_);
lean_ctor_set_uint8(v___x_50_, 1, v___x_49_);
lean_ctor_set_uint8(v___x_50_, 2, v___x_49_);
lean_ctor_set_uint8(v___x_50_, 3, v___x_49_);
v___x_51_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_48_, v___x_50_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_51_);
v___x_53_ = v___x_42_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_a_40_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
else
{
lean_dec(v_a_34_);
lean_dec(v_a_31_);
return v___x_38_;
}
}
else
{
lean_dec(v_a_31_);
lean_dec(v_x_15_);
return v___x_33_;
}
}
else
{
lean_dec(v___x_23_);
lean_dec(v_x_15_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBin___boxed(lean_object* v_x_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Fmt_fmtSimpDeclareEvalBin(v_x_56_, v_a_57_, v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1(){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_67_ = l_Lean_Fmt_fmtAttribute;
v___x_68_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__5));
v___x_69_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___closed__2));
v___x_70_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpDeclareEvalBin___boxed), 3, 0);
v___x_71_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_67_, v___x_68_, v___x_69_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1___boxed(lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1();
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise(lean_object* v_x_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1));
lean_inc(v_x_81_);
v___x_85_ = l_Lean_Syntax_isOfKind(v_x_81_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_x_81_);
v___x_86_ = l_Lean_Fmt_Error_partialFormatter;
v___x_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_a_83_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = l_Lean_Syntax_getArg(v_x_81_, v___x_88_);
v___x_90_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__7));
lean_inc(v___x_89_);
v___x_91_ = l_Lean_Syntax_isOfKind(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v___x_89_);
lean_dec(v_x_81_);
v___x_92_ = l_Lean_Fmt_Error_partialFormatter;
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v_a_83_);
return v___x_93_;
}
else
{
lean_object* v___x_94_; lean_object* v_declareTk_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v_declareTk_95_ = l_Lean_Syntax_getArg(v_x_81_, v___x_94_);
v___x_96_ = l_Lean_Fmt_fmt(v_declareTk_95_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_99_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_96_, 2);
v___x_99_ = l_Lean_Fmt_fmt(v___x_89_, v_a_82_, v_a_98_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v_a_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_99_, 2);
v___x_102_ = lean_unsigned_to_nat(2u);
v___x_103_ = l_Lean_Syntax_getArg(v_x_81_, v___x_102_);
lean_dec(v_x_81_);
v___x_104_ = l_Lean_Fmt_fmt(v___x_103_, v_a_82_, v_a_101_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_121_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_a_106_ = lean_ctor_get(v___x_104_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_121_ == 0)
{
v___x_108_ = v___x_104_;
v_isShared_109_ = v_isSharedCheck_121_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_121_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_110_ = lean_unsigned_to_nat(3u);
v___x_111_ = lean_mk_empty_array_with_capacity(v___x_110_);
v___x_112_ = lean_array_push(v___x_111_, v_a_97_);
v___x_113_ = lean_array_push(v___x_112_, v_a_100_);
v___x_114_ = lean_array_push(v___x_113_, v_a_105_);
v___x_115_ = 0;
v___x_116_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_116_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_116_, 1, v___x_115_);
lean_ctor_set_uint8(v___x_116_, 2, v___x_115_);
lean_ctor_set_uint8(v___x_116_, 3, v___x_115_);
v___x_117_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_114_, v___x_116_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_117_);
v___x_119_ = v___x_108_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_a_106_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
lean_dec(v_a_100_);
lean_dec(v_a_97_);
return v___x_104_;
}
}
else
{
lean_dec(v_a_97_);
lean_dec(v_x_81_);
return v___x_99_;
}
}
else
{
lean_dec(v___x_89_);
lean_dec(v_x_81_);
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___boxed(lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise(v_x_122_, v_a_123_, v_a_124_);
lean_dec_ref(v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1(){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = l_Lean_Fmt_fmtAttribute;
v___x_133_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___closed__1));
v___x_134_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___closed__1));
v___x_135_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpDeclareEvalBinBitwise___boxed), 3, 0);
v___x_136_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_132_, v___x_133_, v___x_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1___boxed(lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1();
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred(lean_object* v_x_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1));
lean_inc(v_x_146_);
v___x_150_ = l_Lean_Syntax_isOfKind(v_x_146_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_x_146_);
v___x_151_ = l_Lean_Fmt_Error_partialFormatter;
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_a_148_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = l_Lean_Syntax_getArg(v_x_146_, v___x_153_);
v___x_155_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBin___closed__7));
lean_inc(v___x_154_);
v___x_156_ = l_Lean_Syntax_isOfKind(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v___x_154_);
lean_dec(v_x_146_);
v___x_157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v_a_148_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v_declareTk_160_; lean_object* v___x_161_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v_declareTk_160_ = l_Lean_Syntax_getArg(v_x_146_, v___x_159_);
v___x_161_ = l_Lean_Fmt_fmt(v_declareTk_160_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
v_a_163_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_161_, 2);
v___x_164_ = l_Lean_Fmt_fmt(v___x_154_, v_a_147_, v_a_163_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v_a_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
v_a_166_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_164_, 2);
v___x_167_ = lean_unsigned_to_nat(2u);
v___x_168_ = l_Lean_Syntax_getArg(v_x_146_, v___x_167_);
lean_dec(v_x_146_);
v___x_169_ = l_Lean_Fmt_fmt(v___x_168_, v_a_147_, v_a_166_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_186_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_a_171_ = lean_ctor_get(v___x_169_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_186_ == 0)
{
v___x_173_ = v___x_169_;
v_isShared_174_ = v_isSharedCheck_186_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_186_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_175_ = lean_unsigned_to_nat(3u);
v___x_176_ = lean_mk_empty_array_with_capacity(v___x_175_);
v___x_177_ = lean_array_push(v___x_176_, v_a_162_);
v___x_178_ = lean_array_push(v___x_177_, v_a_165_);
v___x_179_ = lean_array_push(v___x_178_, v_a_170_);
v___x_180_ = 0;
v___x_181_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_181_, 0, v___x_156_);
lean_ctor_set_uint8(v___x_181_, 1, v___x_180_);
lean_ctor_set_uint8(v___x_181_, 2, v___x_180_);
lean_ctor_set_uint8(v___x_181_, 3, v___x_180_);
v___x_182_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_179_, v___x_181_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_182_);
v___x_184_ = v___x_173_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_a_171_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_dec(v_a_165_);
lean_dec(v_a_162_);
return v___x_169_;
}
}
else
{
lean_dec(v_a_162_);
lean_dec(v_x_146_);
return v___x_164_;
}
}
else
{
lean_dec(v___x_154_);
lean_dec(v_x_146_);
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___boxed(lean_object* v_x_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred(v_x_187_, v_a_188_, v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1(){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = l_Lean_Fmt_fmtAttribute;
v___x_198_ = ((lean_object*)(l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___closed__1));
v___x_199_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___closed__1));
v___x_200_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___boxed), 3, 0);
v___x_201_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_197_, v___x_198_, v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1___boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1();
return v_res_203_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBin___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBin__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBitwise___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBitwise__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Fmt_fmtSimpDeclareEvalBinBoolPred___regBuiltin_Lean_Fmt_fmtSimpDeclareEvalBinBoolPred__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_EvalGround(builtin);
}
#ifdef __cplusplus
}
#endif
