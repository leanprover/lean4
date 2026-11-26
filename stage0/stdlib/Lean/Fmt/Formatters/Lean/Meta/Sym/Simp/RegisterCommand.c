// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Meta.Sym.Simp.RegisterCommand
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Meta.Sym.Simp.RegisterCommand meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__1_value),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__3_value),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__5_value),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__7_value),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(216, 103, 67, 80, 248, 223, 51, 5)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__9_value),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 127, 193, 190, 4, 122, 249, 96)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__10_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__11 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__11_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__10_value),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(76, 77, 233, 157, 88, 19, 246, 173)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__12 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__12_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__13 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__13_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__12_value),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(249, 230, 147, 137, 253, 214, 10, 230)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__14 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__14_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "registerSymSimpAttr"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__15 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__15_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__14_value),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__15_value),LEAN_SCALAR_PTR_LITERAL(89, 239, 54, 61, 160, 98, 3, 108)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__16 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__16_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__17 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__17_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__17_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__18 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__18_value;
static const lean_array_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__19 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__19_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__20 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__20_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__20_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtRegisterSymSimpAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(180, 205, 208, 63, 20, 182, 77, 209)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr(lean_object* v_x_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v_docComment_x3f_53_; lean_object* v___y_54_; lean_object* v___y_55_; 
v___x_50_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__16));
lean_inc(v_x_47_);
v___x_51_ = l_Lean_Syntax_isOfKind(v_x_47_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v_x_47_);
v___x_79_ = l_Lean_Fmt_Error_partialFormatter;
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_a_49_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = l_Lean_Syntax_getArg(v_x_47_, v___x_81_);
v___x_83_ = l_Lean_Syntax_isNone(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_82_);
v___x_85_ = l_Lean_Syntax_matchesNull(v___x_82_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v___x_82_);
lean_dec(v_x_47_);
v___x_86_ = l_Lean_Fmt_Error_partialFormatter;
v___x_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_a_49_);
return v___x_87_;
}
else
{
lean_object* v_docComment_x3f_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_docComment_x3f_88_ = l_Lean_Syntax_getArg(v___x_82_, v___x_81_);
lean_dec(v___x_82_);
v___x_89_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__21));
lean_inc(v_docComment_x3f_88_);
v___x_90_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_docComment_x3f_88_);
lean_dec(v_x_47_);
v___x_91_ = l_Lean_Fmt_Error_partialFormatter;
v___x_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v_a_49_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v_docComment_x3f_88_);
v_docComment_x3f_53_ = v___x_93_;
v___y_54_ = v_a_48_;
v___y_55_ = v_a_49_;
goto v___jp_52_;
}
}
}
else
{
lean_object* v___x_94_; 
lean_dec(v___x_82_);
v___x_94_ = lean_box(0);
v_docComment_x3f_53_ = v___x_94_;
v___y_54_ = v_a_48_;
v___y_55_ = v_a_49_;
goto v___jp_52_;
}
}
v___jp_52_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_56_ = lean_unsigned_to_nat(2u);
v___x_57_ = l_Lean_Syntax_getArg(v_x_47_, v___x_56_);
v___x_58_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__18));
lean_inc(v___x_57_);
v___x_59_ = l_Lean_Syntax_isOfKind(v___x_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec(v___x_57_);
lean_dec(v_docComment_x3f_53_);
lean_dec(v_x_47_);
v___x_60_ = l_Lean_Fmt_Error_partialFormatter;
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___y_55_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; lean_object* v_registerTk_63_; lean_object* v___x_64_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v_registerTk_63_ = l_Lean_Syntax_getArg(v_x_47_, v___x_62_);
lean_dec(v_x_47_);
v___x_64_ = l_Lean_Fmt_fmt(v_registerTk_63_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v_a_66_; lean_object* v___x_67_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
v_a_66_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_a_66_);
lean_dec_ref_known(v___x_64_, 2);
v___x_67_ = l_Lean_Fmt_fmt(v___x_57_, v___y_54_, v_a_66_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v___x_67_, 1);
lean_inc(v_a_69_);
lean_dec_ref_known(v___x_67_, 2);
v___x_70_ = lean_mk_empty_array_with_capacity(v___x_56_);
v___x_71_ = lean_array_push(v___x_70_, v_a_65_);
v___x_72_ = lean_array_push(v___x_71_, v_a_68_);
v___x_73_ = 0;
v___x_74_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_74_, 0, v___x_51_);
lean_ctor_set_uint8(v___x_74_, 1, v___x_73_);
lean_ctor_set_uint8(v___x_74_, 2, v___x_73_);
lean_ctor_set_uint8(v___x_74_, 3, v___x_73_);
v___x_75_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_72_, v___x_74_);
v___x_76_ = lean_box(0);
v___x_77_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__19));
v___x_78_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_53_, v___x_76_, v___x_77_, v___x_75_, v___y_54_, v_a_69_);
return v___x_78_;
}
else
{
lean_dec(v_a_65_);
lean_dec(v_docComment_x3f_53_);
return v___x_67_;
}
}
else
{
lean_dec(v___x_57_);
lean_dec(v_docComment_x3f_53_);
return v___x_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymSimpAttr___boxed(lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Fmt_fmtRegisterSymSimpAttr(v_x_95_, v_a_96_, v_a_97_);
lean_dec_ref(v_a_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1(){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_106_ = l_Lean_Fmt_fmtAttribute;
v___x_107_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymSimpAttr___closed__16));
v___x_108_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___closed__2));
v___x_109_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterSymSimpAttr___boxed), 3, 0);
v___x_110_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_106_, v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1___boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1();
return v_res_112_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSymSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSymSimpAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_RegisterCommand(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_RegisterCommand(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
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
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
}
#ifdef __cplusplus
}
#endif
