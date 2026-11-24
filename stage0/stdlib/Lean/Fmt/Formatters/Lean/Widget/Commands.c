// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Widget.Commands
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Widget.Commands meta import Lean.Parser.Term import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtWidgetInstanceSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtWidgetInstanceSpec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWidgetInstanceSpec___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWidgetInstanceSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWidgetInstanceSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWidgetCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtWidgetCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtWidgetCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Widget"};
static const lean_object* l_Lean_Fmt_fmtWidgetCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtWidgetCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "widgetCmd"};
static const lean_object* l_Lean_Fmt_fmtWidgetCmd___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtWidgetCmd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWidgetCmd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Fmt_fmtWidgetCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 247, 198, 226, 79, 16, 223, 88)}};
static const lean_object* l_Lean_Fmt_fmtWidgetCmd___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtWidgetCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "widgetInstanceSpec"};
static const lean_object* l_Lean_Fmt_fmtWidgetCmd___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtWidgetCmd___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWidgetCmd___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Fmt_fmtWidgetCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 43, 105, 195, 200, 35, 64, 193)}};
static const lean_object* l_Lean_Fmt_fmtWidgetCmd___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtWidgetCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtWidgetCmd___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtWidgetCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtWidgetCmd___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWidgetCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWidgetCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtWidgetCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 42, 114, 67, 218, 34, 132, 240)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtAddWidgetSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "addWidgetSpec"};
static const lean_object* l_Lean_Fmt_fmtAddWidgetSpec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtAddWidgetSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtAddWidgetSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Fmt_fmtAddWidgetSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 146, 251, 200, 206, 220, 208, 83)}};
static const lean_object* l_Lean_Fmt_fmtAddWidgetSpec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtAddWidgetSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtAddWidgetSpec___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtAddWidgetSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtAddWidgetSpec___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtAddWidgetSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Fmt_fmtAddWidgetSpec___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtAddWidgetSpec___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtAddWidgetSpec___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtAddWidgetSpec___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtAddWidgetSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Fmt_fmtAddWidgetSpec___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtAddWidgetSpec___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAddWidgetSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAddWidgetSpec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtAddWidgetSpec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 98, 73, 122, 91, 198, 241, 215)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEraseWidgetSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "eraseWidgetSpec"};
static const lean_object* l_Lean_Fmt_fmtEraseWidgetSpec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEraseWidgetSpec___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtEraseWidgetSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtEraseWidgetSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEraseWidgetSpec___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Fmt_fmtEraseWidgetSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtEraseWidgetSpec___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtEraseWidgetSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 58, 73, 174, 184, 82, 104, 4)}};
static const lean_object* l_Lean_Fmt_fmtEraseWidgetSpec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEraseWidgetSpec___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEraseWidgetSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEraseWidgetSpec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtEraseWidgetSpec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 65, 48, 147, 159, 29, 91, 192)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtShowWidgetSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "showWidgetSpec"};
static const lean_object* l_Lean_Fmt_fmtShowWidgetSpec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtShowWidgetSpec___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtShowWidgetSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtShowWidgetSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtShowWidgetSpec___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Fmt_fmtShowWidgetSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtShowWidgetSpec___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtShowWidgetSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 169, 125, 185, 204, 106, 221, 205)}};
static const lean_object* l_Lean_Fmt_fmtShowWidgetSpec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtShowWidgetSpec___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtShowWidgetSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtShowWidgetSpec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtShowWidgetSpec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 142, 139, 128, 143, 93, 171, 245)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "showPanelWidgetsCmd"};
static const lean_object* l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 47, 106, 136, 147, 253, 78, 115)}};
static const lean_ctor_object l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 207, 30, 126, 74, 89, 231, 190)}};
static const lean_object* l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtShowPanelWidgetsCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtShowPanelWidgetsCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtShowPanelWidgetsCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWidgetCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 153, 173, 73, 48, 240, 213, 50)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWidgetInstanceSpec(lean_object* v_head_4_, lean_object* v_mod_5_, lean_object* v_withTk_x3f_6_, lean_object* v_props_x3f_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Fmt_fmt(v_mod_5_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
v_a_12_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_a_12_);
lean_dec_ref_known(v___x_10_, 2);
v___x_13_ = l_Lean_Fmt_fmt_x3f(v_withTk_x3f_6_, v_a_8_, v_a_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v_a_15_; lean_object* v___y_17_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
v_a_15_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_a_15_);
lean_dec_ref_known(v___x_13_, 2);
if (lean_obj_tag(v_props_x3f_7_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
v___y_17_ = v___x_42_;
goto v___jp_16_;
}
else
{
lean_object* v_val_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
v_val_43_ = lean_ctor_get(v_props_x3f_7_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v_props_x3f_7_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v_props_x3f_7_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_val_43_);
lean_dec(v_props_x3f_7_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_val_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
v___y_17_ = v___x_48_;
goto v___jp_16_;
}
}
}
v___jp_16_:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Fmt_fmt_x3f(v___y_17_, v_a_8_, v_a_15_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_41_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_a_20_ = lean_ctor_get(v___x_18_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_41_ == 0)
{
v___x_22_ = v___x_18_;
v_isShared_23_ = v_isSharedCheck_41_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_41_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_24_ = lean_unsigned_to_nat(2u);
v___x_25_ = lean_mk_empty_array_with_capacity(v___x_24_);
lean_inc_ref(v___x_25_);
v___x_26_ = lean_array_push(v___x_25_, v_head_4_);
v___x_27_ = lean_array_push(v___x_26_, v_a_11_);
v___x_28_ = 1;
v___x_29_ = ((lean_object*)(l_Lean_Fmt_fmtWidgetInstanceSpec___closed__0));
v___x_30_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_27_, v___x_29_);
v___x_31_ = 0;
v___x_32_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_a_14_, v_a_19_, v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_33_, 0, v___x_30_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*1, v___x_28_);
v___x_34_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_34_, 0, v___x_32_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*1, v___x_28_);
v___x_35_ = lean_array_push(v___x_25_, v___x_33_);
v___x_36_ = lean_array_push(v___x_35_, v___x_34_);
v___x_37_ = l_Lean_Fmt_Layouts_blocks(v___x_36_, v___x_28_);
lean_dec_ref(v___x_36_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_37_);
v___x_39_ = v___x_22_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_a_20_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_dec(v_a_14_);
lean_dec(v_a_11_);
lean_dec_ref(v_head_4_);
return v___x_18_;
}
}
}
else
{
lean_dec(v_a_11_);
lean_dec(v_props_x3f_7_);
lean_dec_ref(v_head_4_);
return v___x_13_;
}
}
else
{
lean_dec(v_props_x3f_7_);
lean_dec(v_withTk_x3f_6_);
lean_dec_ref(v_head_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWidgetInstanceSpec___boxed(lean_object* v_head_51_, lean_object* v_mod_52_, lean_object* v_withTk_x3f_53_, lean_object* v_props_x3f_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Fmt_fmtWidgetInstanceSpec(v_head_51_, v_mod_52_, v_withTk_x3f_53_, v_props_x3f_54_, v_a_55_, v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWidgetCmd(lean_object* v_x_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_Fmt_fmtWidgetCmd___closed__3));
lean_inc(v_x_73_);
v___x_77_ = l_Lean_Syntax_isOfKind(v_x_73_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_x_73_);
v___x_78_ = l_Lean_Fmt_Error_partialFormatter;
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v_a_75_);
return v___x_79_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_73_, v___x_80_);
v___x_82_ = ((lean_object*)(l_Lean_Fmt_fmtWidgetCmd___closed__5));
lean_inc(v___x_81_);
v___x_83_ = l_Lean_Syntax_isOfKind(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v___x_81_);
lean_dec(v_x_73_);
v___x_84_ = l_Lean_Fmt_Error_partialFormatter;
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v_a_75_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; lean_object* v_mod_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v_mod_87_ = l_Lean_Syntax_getArg(v___x_81_, v___x_86_);
v___x_88_ = ((lean_object*)(l_Lean_Fmt_fmtWidgetCmd___closed__7));
lean_inc(v_mod_87_);
v___x_89_ = l_Lean_Syntax_isOfKind(v_mod_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_mod_87_);
lean_dec(v___x_81_);
lean_dec(v_x_73_);
v___x_90_ = l_Lean_Fmt_Error_partialFormatter;
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v_a_75_);
return v___x_91_;
}
else
{
lean_object* v_widgetTk_92_; lean_object* v_withTk_x3f_94_; lean_object* v_props_x3f_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_widgetTk_92_ = l_Lean_Syntax_getArg(v_x_73_, v___x_86_);
lean_dec(v_x_73_);
v___x_102_ = l_Lean_Syntax_getArg(v___x_81_, v___x_80_);
lean_dec(v___x_81_);
v___x_103_ = l_Lean_Syntax_isNone(v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_102_);
v___x_105_ = l_Lean_Syntax_matchesNull(v___x_102_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v___x_102_);
lean_dec(v_widgetTk_92_);
lean_dec(v_mod_87_);
v___x_106_ = l_Lean_Fmt_Error_partialFormatter;
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_a_75_);
return v___x_107_;
}
else
{
lean_object* v_withTk_x3f_108_; lean_object* v_props_x3f_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_withTk_x3f_108_ = l_Lean_Syntax_getArg(v___x_102_, v___x_86_);
v_props_x3f_109_ = l_Lean_Syntax_getArg(v___x_102_, v___x_80_);
lean_dec(v___x_102_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v_withTk_x3f_108_);
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v_props_x3f_109_);
v_withTk_x3f_94_ = v___x_110_;
v_props_x3f_95_ = v___x_111_;
v___y_96_ = v_a_74_;
v___y_97_ = v_a_75_;
goto v___jp_93_;
}
}
else
{
lean_object* v___x_112_; 
lean_dec(v___x_102_);
v___x_112_ = lean_box(0);
v_withTk_x3f_94_ = v___x_112_;
v_props_x3f_95_ = v___x_112_;
v___y_96_ = v_a_74_;
v___y_97_ = v_a_75_;
goto v___jp_93_;
}
v___jp_93_:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Fmt_fmt(v_widgetTk_92_, v___y_96_, v___y_97_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v___x_101_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
v_a_100_ = lean_ctor_get(v___x_98_, 1);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_98_, 2);
v___x_101_ = l_Lean_Fmt_fmtWidgetInstanceSpec(v_a_99_, v_mod_87_, v_withTk_x3f_94_, v_props_x3f_95_, v___y_96_, v_a_100_);
return v___x_101_;
}
else
{
lean_dec(v_props_x3f_95_);
lean_dec(v_withTk_x3f_94_);
lean_dec(v_mod_87_);
return v___x_98_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWidgetCmd___boxed(lean_object* v_x_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Fmt_fmtWidgetCmd(v_x_113_, v_a_114_, v_a_115_);
lean_dec_ref(v_a_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1(){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = l_Lean_Fmt_fmtAttribute;
v___x_125_ = ((lean_object*)(l_Lean_Fmt_fmtWidgetCmd___closed__3));
v___x_126_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___closed__2));
v___x_127_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtWidgetCmd___boxed), 3, 0);
v___x_128_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_124_, v___x_125_, v___x_126_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1___boxed(lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1();
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAddWidgetSpec(lean_object* v_x_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Fmt_fmtAddWidgetSpec___closed__1));
lean_inc(v_x_144_);
v___x_148_ = l_Lean_Syntax_isOfKind(v_x_144_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_x_144_);
v___x_149_ = l_Lean_Fmt_Error_partialFormatter;
v___x_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_a_146_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = l_Lean_Syntax_getArg(v_x_144_, v___x_151_);
v___x_153_ = ((lean_object*)(l_Lean_Fmt_fmtAddWidgetSpec___closed__5));
lean_inc(v___x_152_);
v___x_154_ = l_Lean_Syntax_isOfKind(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v___x_152_);
lean_dec(v_x_144_);
v___x_155_ = l_Lean_Fmt_Error_partialFormatter;
v___x_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_a_146_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = l_Lean_Syntax_getArg(v_x_144_, v___x_157_);
lean_dec(v_x_144_);
v___x_159_ = ((lean_object*)(l_Lean_Fmt_fmtWidgetCmd___closed__5));
lean_inc(v___x_158_);
v___x_160_ = l_Lean_Syntax_isOfKind(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v___x_158_);
lean_dec(v___x_152_);
v___x_161_ = l_Lean_Fmt_Error_partialFormatter;
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_146_);
return v___x_162_;
}
else
{
lean_object* v_mod_163_; lean_object* v_withTk_x3f_165_; lean_object* v_props_x3f_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_mod_163_ = l_Lean_Syntax_getArg(v___x_158_, v___x_151_);
v___x_173_ = ((lean_object*)(l_Lean_Fmt_fmtWidgetCmd___closed__7));
lean_inc(v_mod_163_);
v___x_174_ = l_Lean_Syntax_isOfKind(v_mod_163_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_mod_163_);
lean_dec(v___x_158_);
lean_dec(v___x_152_);
v___x_175_ = l_Lean_Fmt_Error_partialFormatter;
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_146_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = l_Lean_Syntax_getArg(v___x_158_, v___x_157_);
lean_dec(v___x_158_);
v___x_178_ = l_Lean_Syntax_isNone(v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_177_);
v___x_180_ = l_Lean_Syntax_matchesNull(v___x_177_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v___x_177_);
lean_dec(v_mod_163_);
lean_dec(v___x_152_);
v___x_181_ = l_Lean_Fmt_Error_partialFormatter;
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_146_);
return v___x_182_;
}
else
{
lean_object* v_withTk_x3f_183_; lean_object* v_props_x3f_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_withTk_x3f_183_ = l_Lean_Syntax_getArg(v___x_177_, v___x_151_);
v_props_x3f_184_ = l_Lean_Syntax_getArg(v___x_177_, v___x_157_);
lean_dec(v___x_177_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v_withTk_x3f_183_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_props_x3f_184_);
v_withTk_x3f_165_ = v___x_185_;
v_props_x3f_166_ = v___x_186_;
v___y_167_ = v_a_145_;
v___y_168_ = v_a_146_;
goto v___jp_164_;
}
}
else
{
lean_object* v___x_187_; 
lean_dec(v___x_177_);
v___x_187_ = lean_box(0);
v_withTk_x3f_165_ = v___x_187_;
v_props_x3f_166_ = v___x_187_;
v___y_167_ = v_a_145_;
v___y_168_ = v_a_146_;
goto v___jp_164_;
}
}
v___jp_164_:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Fmt_fmt(v___x_152_, v___y_167_, v___y_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v_a_171_; lean_object* v___x_172_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
v_a_171_ = lean_ctor_get(v___x_169_, 1);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_169_, 2);
v___x_172_ = l_Lean_Fmt_fmtWidgetInstanceSpec(v_a_170_, v_mod_163_, v_withTk_x3f_165_, v_props_x3f_166_, v___y_167_, v_a_171_);
return v___x_172_;
}
else
{
lean_dec(v_props_x3f_166_);
lean_dec(v_withTk_x3f_165_);
lean_dec(v_mod_163_);
return v___x_169_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAddWidgetSpec___boxed(lean_object* v_x_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Fmt_fmtAddWidgetSpec(v_x_188_, v_a_189_, v_a_190_);
lean_dec_ref(v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1(){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_198_ = l_Lean_Fmt_fmtAttribute;
v___x_199_ = ((lean_object*)(l_Lean_Fmt_fmtAddWidgetSpec___closed__1));
v___x_200_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___closed__1));
v___x_201_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAddWidgetSpec___boxed), 3, 0);
v___x_202_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_198_, v___x_199_, v___x_200_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1___boxed(lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1();
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEraseWidgetSpec(lean_object* v_x_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Fmt_fmtEraseWidgetSpec___closed__1));
lean_inc(v_x_210_);
v___x_214_ = l_Lean_Syntax_isOfKind(v_x_210_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_x_210_);
v___x_215_ = l_Lean_Fmt_Error_partialFormatter;
v___x_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_a_212_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = l_Lean_Syntax_getArg(v_x_210_, v___x_217_);
v___x_219_ = ((lean_object*)(l_Lean_Fmt_fmtWidgetCmd___closed__7));
lean_inc(v___x_218_);
v___x_220_ = l_Lean_Syntax_isOfKind(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v___x_218_);
lean_dec(v_x_210_);
v___x_221_ = l_Lean_Fmt_Error_partialFormatter;
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_a_212_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v_minusTk_224_; lean_object* v___x_225_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v_minusTk_224_ = l_Lean_Syntax_getArg(v_x_210_, v___x_223_);
lean_dec(v_x_210_);
v___x_225_ = l_Lean_Fmt_fmt(v_minusTk_224_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v_a_227_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
v_a_227_ = lean_ctor_get(v___x_225_, 1);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_225_, 2);
v___x_228_ = l_Lean_Fmt_fmt(v___x_218_, v_a_211_, v_a_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_239_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_a_230_ = lean_ctor_get(v___x_228_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_239_ == 0)
{
v___x_232_ = v___x_228_;
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = 0;
v___x_235_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_226_, v_a_229_, v___x_234_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_235_);
v___x_237_ = v___x_232_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_a_230_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_dec(v_a_226_);
return v___x_228_;
}
}
else
{
lean_dec(v___x_218_);
return v___x_225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEraseWidgetSpec___boxed(lean_object* v_x_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Fmt_fmtEraseWidgetSpec(v_x_240_, v_a_241_, v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_250_ = l_Lean_Fmt_fmtAttribute;
v___x_251_ = ((lean_object*)(l_Lean_Fmt_fmtEraseWidgetSpec___closed__1));
v___x_252_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___closed__1));
v___x_253_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEraseWidgetSpec___boxed), 3, 0);
v___x_254_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_250_, v___x_251_, v___x_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1___boxed(lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtShowWidgetSpec(lean_object* v_x_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Fmt_fmtShowWidgetSpec___closed__1));
lean_inc(v_x_262_);
v___x_266_ = l_Lean_Syntax_isOfKind(v_x_262_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_x_262_);
v___x_267_ = l_Lean_Fmt_Error_partialFormatter;
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_264_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = l_Lean_Syntax_getArg(v_x_262_, v___x_269_);
lean_dec(v_x_262_);
v___x_271_ = ((lean_object*)(l_Lean_Fmt_fmtAddWidgetSpec___closed__1));
lean_inc(v___x_270_);
v___x_272_ = l_Lean_Syntax_isOfKind(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_Fmt_fmtEraseWidgetSpec___closed__1));
lean_inc(v___x_270_);
v___x_274_ = l_Lean_Syntax_isOfKind(v___x_270_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v___x_270_);
v___x_275_ = l_Lean_Fmt_Error_partialFormatter;
v___x_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v_a_264_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Fmt_fmt(v___x_270_, v_a_263_, v_a_264_);
return v___x_277_;
}
}
else
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Fmt_fmt(v___x_270_, v_a_263_, v_a_264_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtShowWidgetSpec___boxed(lean_object* v_x_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Fmt_fmtShowWidgetSpec(v_x_279_, v_a_280_, v_a_281_);
lean_dec_ref(v_a_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1(){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_289_ = l_Lean_Fmt_fmtAttribute;
v___x_290_ = ((lean_object*)(l_Lean_Fmt_fmtShowWidgetSpec___closed__1));
v___x_291_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___closed__1));
v___x_292_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtShowWidgetSpec___boxed), 3, 0);
v___x_293_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_289_, v___x_290_, v___x_291_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1___boxed(lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1();
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtShowPanelWidgetsCmd(lean_object* v_x_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1));
lean_inc(v_x_302_);
v___x_306_ = l_Lean_Syntax_isOfKind(v_x_302_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_x_302_);
v___x_307_ = l_Lean_Fmt_Error_partialFormatter;
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_a_304_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v_showTk_310_; lean_object* v___x_311_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v_showTk_310_ = l_Lean_Syntax_getArg(v_x_302_, v___x_309_);
v___x_311_ = l_Lean_Fmt_fmt(v_showTk_310_, v_a_303_, v_a_304_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v_lbTk_315_; lean_object* v___x_316_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
v_a_313_ = lean_ctor_get(v___x_311_, 1);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_311_, 2);
v___x_314_ = lean_unsigned_to_nat(1u);
v_lbTk_315_ = l_Lean_Syntax_getArg(v_x_302_, v___x_314_);
v___x_316_ = l_Lean_Fmt_fmt(v_lbTk_315_, v_a_303_, v_a_313_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_specs_321_; lean_object* v___x_322_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
v_a_318_ = lean_ctor_get(v___x_316_, 1);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_316_, 2);
v___x_319_ = lean_unsigned_to_nat(2u);
v___x_320_ = l_Lean_Syntax_getArg(v_x_302_, v___x_319_);
v_specs_321_ = l_Lean_Syntax_getArgs(v___x_320_);
lean_dec(v___x_320_);
v___x_322_ = l_Lean_Fmt_fmtTSepArray___redArg(v_specs_321_, v_a_303_, v_a_318_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v_rbTk_326_; lean_object* v___x_327_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
v_a_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_322_, 2);
v___x_325_ = lean_unsigned_to_nat(3u);
v_rbTk_326_ = l_Lean_Syntax_getArg(v_x_302_, v___x_325_);
lean_dec(v_x_302_);
v___x_327_ = l_Lean_Fmt_fmt(v_rbTk_326_, v_a_303_, v_a_324_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_345_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_a_329_ = lean_ctor_get(v___x_327_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_345_ == 0)
{
v___x_331_ = v___x_327_;
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_333_ = ((lean_object*)(l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__2));
v___x_334_ = 0;
v___x_335_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_335_, 0, v___x_334_);
lean_ctor_set_uint8(v___x_335_, 1, v___x_306_);
v___x_336_ = l_Lean_Fmt_Layouts_collection(v___x_333_, v_a_317_, v_a_323_, v_a_328_, v___x_335_);
lean_dec(v_a_323_);
v___x_337_ = lean_mk_empty_array_with_capacity(v___x_319_);
v___x_338_ = lean_array_push(v___x_337_, v_a_312_);
v___x_339_ = lean_array_push(v___x_338_, v___x_336_);
v___x_340_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_340_, 0, v___x_306_);
lean_ctor_set_uint8(v___x_340_, 1, v___x_334_);
lean_ctor_set_uint8(v___x_340_, 2, v___x_334_);
lean_ctor_set_uint8(v___x_340_, 3, v___x_334_);
v___x_341_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_339_, v___x_340_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_341_);
v___x_343_ = v___x_331_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_a_329_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_dec(v_a_323_);
lean_dec(v_a_317_);
lean_dec(v_a_312_);
return v___x_327_;
}
}
else
{
lean_object* v_a_346_; lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_317_);
lean_dec(v_a_312_);
lean_dec(v_x_302_);
v_a_346_ = lean_ctor_get(v___x_322_, 0);
v_a_347_ = lean_ctor_get(v___x_322_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_322_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_inc(v_a_346_);
lean_dec(v___x_322_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_346_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_dec(v_a_312_);
lean_dec(v_x_302_);
return v___x_316_;
}
}
else
{
lean_dec(v_x_302_);
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtShowPanelWidgetsCmd___boxed(lean_object* v_x_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Fmt_fmtShowPanelWidgetsCmd(v_x_355_, v_a_356_, v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1(){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_365_ = l_Lean_Fmt_fmtAttribute;
v___x_366_ = ((lean_object*)(l_Lean_Fmt_fmtShowPanelWidgetsCmd___closed__1));
v___x_367_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___closed__1));
v___x_368_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtShowPanelWidgetsCmd___boxed), 3, 0);
v___x_369_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_365_, v___x_366_, v___x_367_, v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1___boxed(lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1();
return v_res_371_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Widget_Commands(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtWidgetCmd___regBuiltin_Lean_Fmt_fmtWidgetCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtAddWidgetSpec___regBuiltin_Lean_Fmt_fmtAddWidgetSpec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtEraseWidgetSpec___regBuiltin_Lean_Fmt_fmtEraseWidgetSpec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowWidgetSpec___regBuiltin_Lean_Fmt_fmtShowWidgetSpec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Widget_Commands_0__Lean_Fmt_fmtShowPanelWidgetsCmd___regBuiltin_Lean_Fmt_fmtShowPanelWidgetsCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Widget_Commands(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Widget_Commands(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Widget_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Widget_Commands(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Widget_Commands(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Widget_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Widget_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Widget_Commands(builtin);
}
#ifdef __cplusplus
}
#endif
