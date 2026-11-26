// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Elab.Tactic.Config
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Elab.Tactic.Config meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtDeclareConfigElabLegacy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtDeclareConfigElabLegacy___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeclareConfigElabLegacy___closed__0_value;
static const lean_array_object l_Lean_Fmt_fmtDeclareConfigElabLegacy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtDeclareConfigElabLegacy___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeclareConfigElabLegacy___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareConfigElabLegacy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareConfigElabLegacy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConfigElabLegacy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConfigElabLegacy___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtConfigElabLegacy___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtConfigElabLegacy___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtConfigElabLegacy___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configElab"};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 113, 199, 142, 5, 77, 11, 142)}};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtConfigElabLegacy___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtConfigElabLegacy___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtConfigElabLegacy___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__10_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__10_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtConfigElabLegacy___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__10_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtConfigElabLegacy___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigElabLegacy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigElabLegacy___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtConfigElabLegacy"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(19, 11, 11, 80, 189, 49, 73, 242)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "commandConfigElab"};
static const lean_object* l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 198, 218, 173, 29, 96, 128, 77)}};
static const lean_object* l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCommandConfigElabLegacy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCommandConfigElabLegacy___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "fmtCommandConfigElabLegacy"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConfigElabLegacy___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 171, 141, 192, 91, 93, 90, 17)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareConfigElabLegacy(lean_object* v_docComment_x3f_6_, lean_object* v_declTk_7_, lean_object* v_elabId_8_, lean_object* v_typeId_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Fmt_fmt(v_declTk_7_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
v_a_14_ = lean_ctor_get(v___x_12_, 1);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_12_, 2);
v___x_15_ = l_Lean_Fmt_fmt(v_elabId_8_, v_a_10_, v_a_14_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v___x_15_, 1);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_15_, 2);
v___x_18_ = l_Lean_Fmt_fmt(v_typeId_9_, v_a_10_, v_a_17_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v_a_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
v_a_20_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_18_, 2);
v___x_21_ = lean_unsigned_to_nat(3u);
v___x_22_ = lean_mk_empty_array_with_capacity(v___x_21_);
v___x_23_ = lean_array_push(v___x_22_, v_a_13_);
v___x_24_ = lean_array_push(v___x_23_, v_a_16_);
v___x_25_ = lean_array_push(v___x_24_, v_a_19_);
v___x_26_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareConfigElabLegacy___closed__0));
v___x_27_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_25_, v___x_26_);
v___x_28_ = lean_box(0);
v___x_29_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareConfigElabLegacy___closed__1));
v___x_30_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_6_, v___x_28_, v___x_29_, v___x_27_, v_a_10_, v_a_20_);
return v___x_30_;
}
else
{
lean_dec(v_a_16_);
lean_dec(v_a_13_);
lean_dec(v_docComment_x3f_6_);
return v___x_18_;
}
}
else
{
lean_dec(v_a_13_);
lean_dec(v_typeId_9_);
lean_dec(v_docComment_x3f_6_);
return v___x_15_;
}
}
else
{
lean_dec(v_typeId_9_);
lean_dec(v_elabId_8_);
lean_dec(v_docComment_x3f_6_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareConfigElabLegacy___boxed(lean_object* v_docComment_x3f_31_, lean_object* v_declTk_32_, lean_object* v_elabId_33_, lean_object* v_typeId_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Fmt_fmtDeclareConfigElabLegacy(v_docComment_x3f_31_, v_declTk_32_, v_elabId_33_, v_typeId_34_, v_a_35_, v_a_36_);
lean_dec_ref(v_a_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigElabLegacy(lean_object* v_x_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_docComment_x3f_62_; lean_object* v___y_63_; lean_object* v___y_64_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Fmt_fmtConfigElabLegacy___closed__6));
lean_inc(v_x_58_);
v___x_80_ = l_Lean_Syntax_isOfKind(v_x_58_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_x_58_);
v___x_81_ = l_Lean_Fmt_Error_partialFormatter;
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_60_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_Syntax_getArg(v_x_58_, v___x_83_);
v___x_85_ = l_Lean_Syntax_isNone(v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_84_);
v___x_87_ = l_Lean_Syntax_matchesNull(v___x_84_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v___x_84_);
lean_dec(v_x_58_);
v___x_88_ = l_Lean_Fmt_Error_partialFormatter;
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_a_60_);
return v___x_89_;
}
else
{
lean_object* v_docComment_x3f_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_docComment_x3f_90_ = l_Lean_Syntax_getArg(v___x_84_, v___x_83_);
lean_dec(v___x_84_);
v___x_91_ = ((lean_object*)(l_Lean_Fmt_fmtConfigElabLegacy___closed__10));
lean_inc(v_docComment_x3f_90_);
v___x_92_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_docComment_x3f_90_);
lean_dec(v_x_58_);
v___x_93_ = l_Lean_Fmt_Error_partialFormatter;
v___x_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v_a_60_);
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_docComment_x3f_90_);
v_docComment_x3f_62_ = v___x_95_;
v___y_63_ = v_a_59_;
v___y_64_ = v_a_60_;
goto v___jp_61_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v___x_84_);
v___x_96_ = lean_box(0);
v_docComment_x3f_62_ = v___x_96_;
v___y_63_ = v_a_59_;
v___y_64_ = v_a_60_;
goto v___jp_61_;
}
}
v___jp_61_:
{
lean_object* v___x_65_; lean_object* v_elabId_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_65_ = lean_unsigned_to_nat(2u);
v_elabId_66_ = l_Lean_Syntax_getArg(v_x_58_, v___x_65_);
v___x_67_ = ((lean_object*)(l_Lean_Fmt_fmtConfigElabLegacy___closed__1));
lean_inc(v_elabId_66_);
v___x_68_ = l_Lean_Syntax_isOfKind(v_elabId_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_elabId_66_);
lean_dec(v_docComment_x3f_62_);
lean_dec(v_x_58_);
v___x_69_ = l_Lean_Fmt_Error_partialFormatter;
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___y_64_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v_typeId_72_; uint8_t v___x_73_; 
v___x_71_ = lean_unsigned_to_nat(3u);
v_typeId_72_ = l_Lean_Syntax_getArg(v_x_58_, v___x_71_);
lean_inc(v_typeId_72_);
v___x_73_ = l_Lean_Syntax_isOfKind(v_typeId_72_, v___x_67_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_typeId_72_);
lean_dec(v_elabId_66_);
lean_dec(v_docComment_x3f_62_);
lean_dec(v_x_58_);
v___x_74_ = l_Lean_Fmt_Error_partialFormatter;
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___y_64_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v_declTk_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(1u);
v_declTk_77_ = l_Lean_Syntax_getArg(v_x_58_, v___x_76_);
lean_dec(v_x_58_);
v___x_78_ = l_Lean_Fmt_fmtDeclareConfigElabLegacy(v_docComment_x3f_62_, v_declTk_77_, v_elabId_66_, v_typeId_72_, v___y_63_, v___y_64_);
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConfigElabLegacy___boxed(lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Fmt_fmtConfigElabLegacy(v_x_97_, v_a_98_, v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1(){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = l_Lean_Fmt_fmtAttribute;
v___x_109_ = ((lean_object*)(l_Lean_Fmt_fmtConfigElabLegacy___closed__6));
v___x_110_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___closed__2));
v___x_111_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConfigElabLegacy___boxed), 3, 0);
v___x_112_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_108_, v___x_109_, v___x_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1___boxed(lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1();
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCommandConfigElabLegacy(lean_object* v_x_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_docComment_x3f_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1));
lean_inc(v_x_121_);
v___x_143_ = l_Lean_Syntax_isOfKind(v_x_121_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_x_121_);
v___x_144_ = l_Lean_Fmt_Error_partialFormatter;
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_a_123_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l_Lean_Syntax_getArg(v_x_121_, v___x_146_);
v___x_148_ = l_Lean_Syntax_isNone(v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_147_);
v___x_150_ = l_Lean_Syntax_matchesNull(v___x_147_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v___x_147_);
lean_dec(v_x_121_);
v___x_151_ = l_Lean_Fmt_Error_partialFormatter;
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_a_123_);
return v___x_152_;
}
else
{
lean_object* v_docComment_x3f_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_docComment_x3f_153_ = l_Lean_Syntax_getArg(v___x_147_, v___x_146_);
lean_dec(v___x_147_);
v___x_154_ = ((lean_object*)(l_Lean_Fmt_fmtConfigElabLegacy___closed__10));
lean_inc(v_docComment_x3f_153_);
v___x_155_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_docComment_x3f_153_);
lean_dec(v_x_121_);
v___x_156_ = l_Lean_Fmt_Error_partialFormatter;
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_123_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v_docComment_x3f_153_);
v_docComment_x3f_125_ = v___x_158_;
v___y_126_ = v_a_122_;
v___y_127_ = v_a_123_;
goto v___jp_124_;
}
}
}
else
{
lean_object* v___x_159_; 
lean_dec(v___x_147_);
v___x_159_ = lean_box(0);
v_docComment_x3f_125_ = v___x_159_;
v___y_126_ = v_a_122_;
v___y_127_ = v_a_123_;
goto v___jp_124_;
}
}
v___jp_124_:
{
lean_object* v___x_128_; lean_object* v_elabId_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_128_ = lean_unsigned_to_nat(2u);
v_elabId_129_ = l_Lean_Syntax_getArg(v_x_121_, v___x_128_);
v___x_130_ = ((lean_object*)(l_Lean_Fmt_fmtConfigElabLegacy___closed__1));
lean_inc(v_elabId_129_);
v___x_131_ = l_Lean_Syntax_isOfKind(v_elabId_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_elabId_129_);
lean_dec(v_docComment_x3f_125_);
lean_dec(v_x_121_);
v___x_132_ = l_Lean_Fmt_Error_partialFormatter;
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___y_127_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; lean_object* v_typeId_135_; uint8_t v___x_136_; 
v___x_134_ = lean_unsigned_to_nat(3u);
v_typeId_135_ = l_Lean_Syntax_getArg(v_x_121_, v___x_134_);
lean_inc(v_typeId_135_);
v___x_136_ = l_Lean_Syntax_isOfKind(v_typeId_135_, v___x_130_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_typeId_135_);
lean_dec(v_elabId_129_);
lean_dec(v_docComment_x3f_125_);
lean_dec(v_x_121_);
v___x_137_ = l_Lean_Fmt_Error_partialFormatter;
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___y_127_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v_declTk_140_; lean_object* v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v_declTk_140_ = l_Lean_Syntax_getArg(v_x_121_, v___x_139_);
lean_dec(v_x_121_);
v___x_141_ = l_Lean_Fmt_fmtDeclareConfigElabLegacy(v_docComment_x3f_125_, v_declTk_140_, v_elabId_129_, v_typeId_135_, v___y_126_, v___y_127_);
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCommandConfigElabLegacy___boxed(lean_object* v_x_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Fmt_fmtCommandConfigElabLegacy(v_x_160_, v_a_161_, v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1(){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_170_ = l_Lean_Fmt_fmtAttribute;
v___x_171_ = ((lean_object*)(l_Lean_Fmt_fmtCommandConfigElabLegacy___closed__1));
v___x_172_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___closed__1));
v___x_173_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCommandConfigElabLegacy___boxed), 3, 0);
v___x_174_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_170_, v___x_171_, v___x_172_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1___boxed(lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1();
return v_res_176_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtConfigElabLegacy___regBuiltin_Lean_Fmt_fmtConfigElabLegacy__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config_0__Lean_Fmt_fmtCommandConfigElabLegacy___regBuiltin_Lean_Fmt_fmtCommandConfigElabLegacy__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin);
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
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Elab_Tactic_Config(builtin);
}
#ifdef __cplusplus
}
#endif
