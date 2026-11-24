// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Ext
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Ext import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExtIff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtExtIff___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtExtIff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtExtIff___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExtIff___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtExtIff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Fmt_fmtExtIff___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtExtIff___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtExtIff___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extIff"};
static const lean_object* l_Lean_Fmt_fmtExtIff___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtExtIff___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtExtIff___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtIff___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtIff___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtIff___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 87, 43, 146, 87, 18, 162, 246)}};
static const lean_object* l_Lean_Fmt_fmtExtIff___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtExtIff___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtIff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtIff___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtExtIff"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 25, 65, 213, 61, 62, 234, 76)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExtFlat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extFlat"};
static const lean_object* l_Lean_Fmt_fmtExtFlat___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExtFlat___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExtFlat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtFlat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtFlat___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtFlat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtFlat___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtFlat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtFlat___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtExtFlat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 244, 20, 128, 134, 196, 58, 22)}};
static const lean_object* l_Lean_Fmt_fmtExtFlat___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExtFlat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtFlat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtFlat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtExtFlat"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 214, 122, 133, 190, 6, 120, 238)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExtAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Fmt_fmtExtAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExtAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExtAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtExtAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExtAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtExtAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 19, 191, 105, 197, 110, 148, 94)}};
static const lean_object* l_Lean_Fmt_fmtExtAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExtAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtExtAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 20, 126, 179, 89, 53, 55, 193)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Fmt_fmtTacticExt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtTacticExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtTacticExt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtTacticExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ext"};
static const lean_object* l_Lean_Fmt_fmtTacticExt___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 70, 231, 255, 233, 213, 189, 46)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__3_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtExtAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 8, 190, 90, 148, 21, 56, 73)}};
static const lean_object* l_Lean_Fmt_fmtTacticExt___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtTacticExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtTacticExt___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtTacticExt___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticExt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtTacticExt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 1, 50, 91, 185, 198, 135, 105)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticExt1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticExt1___"};
static const lean_object* l_Lean_Fmt_fmtTacticExt1___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticExt1___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticExt1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticExt1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticExt1___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticExt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 70, 231, 255, 233, 213, 189, 46)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticExt1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticExt1___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtTacticExt1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 111, 128, 11, 149, 239, 35, 35)}};
static const lean_object* l_Lean_Fmt_fmtTacticExt1___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticExt1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticExt1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticExt1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtTacticExt1"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExtIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 222, 190, 11, 75, 115, 13, 38)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtIff(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtExtIff___closed__4));
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
lean_object* v___x_17_; lean_object* v_lbTk_18_; lean_object* v___x_19_; lean_object* v_iffTk_20_; lean_object* v___x_21_; lean_object* v_colonEqTk_22_; lean_object* v___x_23_; lean_object* v_falseTk_24_; lean_object* v___x_25_; lean_object* v_rbTk_26_; lean_object* v___x_27_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v_lbTk_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
v___x_19_ = lean_unsigned_to_nat(1u);
v_iffTk_20_ = l_Lean_Syntax_getArg(v_x_10_, v___x_19_);
v___x_21_ = lean_unsigned_to_nat(2u);
v_colonEqTk_22_ = l_Lean_Syntax_getArg(v_x_10_, v___x_21_);
v___x_23_ = lean_unsigned_to_nat(3u);
v_falseTk_24_ = l_Lean_Syntax_getArg(v_x_10_, v___x_23_);
v___x_25_ = lean_unsigned_to_nat(4u);
v_rbTk_26_ = l_Lean_Syntax_getArg(v_x_10_, v___x_25_);
lean_dec(v_x_10_);
v___x_27_ = l_Lean_Fmt_fmtNamedArgumentTerm(v_lbTk_18_, v_iffTk_20_, v_colonEqTk_22_, v_falseTk_24_, v_rbTk_26_, v_a_11_, v_a_12_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtIff___boxed(lean_object* v_x_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Fmt_fmtExtIff(v_x_28_, v_a_29_, v_a_30_);
lean_dec_ref(v_a_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1(){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_39_ = l_Lean_Fmt_fmtAttribute;
v___x_40_ = ((lean_object*)(l_Lean_Fmt_fmtExtIff___closed__4));
v___x_41_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___closed__2));
v___x_42_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExtIff___boxed), 3, 0);
v___x_43_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_39_, v___x_40_, v___x_41_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1___boxed(lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtFlat(lean_object* v_x_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_Fmt_fmtExtFlat___closed__1));
lean_inc(v_x_52_);
v___x_56_ = l_Lean_Syntax_isOfKind(v_x_52_, v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_x_52_);
v___x_57_ = l_Lean_Fmt_Error_partialFormatter;
v___x_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v_a_54_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v_lbTk_60_; lean_object* v___x_61_; lean_object* v_flatTk_62_; lean_object* v___x_63_; lean_object* v_colonEqTk_64_; lean_object* v___x_65_; lean_object* v_falseTk_66_; lean_object* v___x_67_; lean_object* v_rbTk_68_; lean_object* v___x_69_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v_lbTk_60_ = l_Lean_Syntax_getArg(v_x_52_, v___x_59_);
v___x_61_ = lean_unsigned_to_nat(1u);
v_flatTk_62_ = l_Lean_Syntax_getArg(v_x_52_, v___x_61_);
v___x_63_ = lean_unsigned_to_nat(2u);
v_colonEqTk_64_ = l_Lean_Syntax_getArg(v_x_52_, v___x_63_);
v___x_65_ = lean_unsigned_to_nat(3u);
v_falseTk_66_ = l_Lean_Syntax_getArg(v_x_52_, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(4u);
v_rbTk_68_ = l_Lean_Syntax_getArg(v_x_52_, v___x_67_);
lean_dec(v_x_52_);
v___x_69_ = l_Lean_Fmt_fmtNamedArgumentTerm(v_lbTk_60_, v_flatTk_62_, v_colonEqTk_64_, v_falseTk_66_, v_rbTk_68_, v_a_53_, v_a_54_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtFlat___boxed(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Fmt_fmtExtFlat(v_x_70_, v_a_71_, v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1(){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = l_Lean_Fmt_fmtAttribute;
v___x_81_ = ((lean_object*)(l_Lean_Fmt_fmtExtFlat___closed__1));
v___x_82_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___closed__1));
v___x_83_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExtFlat___boxed), 3, 0);
v___x_84_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_80_, v___x_81_, v___x_82_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1___boxed(lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtAttr(lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_146_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; 
v___x_96_ = ((lean_object*)(l_Lean_Fmt_fmtExtAttr___closed__1));
lean_inc(v_x_93_);
v___x_97_ = l_Lean_Syntax_isOfKind(v_x_93_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_x_93_);
v___x_166_ = l_Lean_Fmt_Error_partialFormatter;
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_95_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v_extTk_169_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v_prio_x3f_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___x_190_; lean_object* v___y_192_; lean_object* v_extFlat_x3f_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v_extIff_x3f_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v_extTk_169_ = l_Lean_Syntax_getArg(v_x_93_, v___x_168_);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_222_ = l_Lean_Syntax_getArg(v_x_93_, v___x_190_);
v___x_223_ = l_Lean_Syntax_isNone(v___x_222_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; 
lean_inc(v___x_222_);
v___x_224_ = l_Lean_Syntax_matchesNull(v___x_222_, v___x_190_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v___x_222_);
lean_dec(v_extTk_169_);
lean_dec(v_x_93_);
v___x_225_ = l_Lean_Fmt_Error_partialFormatter;
v___x_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_a_95_);
return v___x_226_;
}
else
{
lean_object* v_extIff_x3f_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_extIff_x3f_227_ = l_Lean_Syntax_getArg(v___x_222_, v___x_168_);
lean_dec(v___x_222_);
v___x_228_ = ((lean_object*)(l_Lean_Fmt_fmtExtIff___closed__4));
lean_inc(v_extIff_x3f_227_);
v___x_229_ = l_Lean_Syntax_isOfKind(v_extIff_x3f_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v_extIff_x3f_227_);
lean_dec(v_extTk_169_);
lean_dec(v_x_93_);
v___x_230_ = l_Lean_Fmt_Error_partialFormatter;
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_95_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_extIff_x3f_227_);
v_extIff_x3f_206_ = v___x_232_;
v___y_207_ = v_a_94_;
v___y_208_ = v_a_95_;
goto v___jp_205_;
}
}
}
else
{
lean_object* v___x_233_; 
lean_dec(v___x_222_);
v___x_233_ = lean_box(0);
v_extIff_x3f_206_ = v___x_233_;
v___y_207_ = v_a_94_;
v___y_208_ = v_a_95_;
goto v___jp_205_;
}
v___jp_170_:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Fmt_fmt(v_extTk_169_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
if (lean_obj_tag(v___y_171_) == 0)
{
lean_object* v_a_177_; lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
v_a_178_ = lean_ctor_get(v___x_176_, 1);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_176_, 2);
v___x_179_ = lean_box(0);
v___y_146_ = v___y_174_;
v___y_147_ = v___y_172_;
v___y_148_ = v_a_177_;
v___y_149_ = v_prio_x3f_173_;
v___y_150_ = v_a_178_;
v___y_151_ = v___x_179_;
goto v___jp_145_;
}
else
{
lean_object* v_a_180_; lean_object* v_a_181_; lean_object* v_val_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_a_180_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_180_);
v_a_181_ = lean_ctor_get(v___x_176_, 1);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_176_, 2);
v_val_182_ = lean_ctor_get(v___y_171_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___y_171_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___y_171_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_val_182_);
lean_dec(v___y_171_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_val_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v___y_146_ = v___y_174_;
v___y_147_ = v___y_172_;
v___y_148_ = v_a_180_;
v___y_149_ = v_prio_x3f_173_;
v___y_150_ = v_a_181_;
v___y_151_ = v___x_187_;
goto v___jp_145_;
}
}
}
}
else
{
lean_dec(v_prio_x3f_173_);
lean_dec(v___y_172_);
lean_dec(v___y_171_);
return v___x_176_;
}
}
v___jp_191_:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = lean_unsigned_to_nat(3u);
v___x_197_ = l_Lean_Syntax_getArg(v_x_93_, v___x_196_);
lean_dec(v_x_93_);
v___x_198_ = l_Lean_Syntax_isNone(v___x_197_);
if (v___x_198_ == 0)
{
uint8_t v___x_199_; 
lean_inc(v___x_197_);
v___x_199_ = l_Lean_Syntax_matchesNull(v___x_197_, v___x_190_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v___x_197_);
lean_dec(v_extFlat_x3f_193_);
lean_dec(v___y_192_);
lean_dec(v_extTk_169_);
v___x_200_ = l_Lean_Fmt_Error_partialFormatter;
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___y_195_);
return v___x_201_;
}
else
{
lean_object* v_prio_x3f_202_; lean_object* v___x_203_; 
v_prio_x3f_202_ = l_Lean_Syntax_getArg(v___x_197_, v___x_168_);
lean_dec(v___x_197_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_prio_x3f_202_);
v___y_171_ = v___y_192_;
v___y_172_ = v_extFlat_x3f_193_;
v_prio_x3f_173_ = v___x_203_;
v___y_174_ = v___y_194_;
v___y_175_ = v___y_195_;
goto v___jp_170_;
}
}
else
{
lean_object* v___x_204_; 
lean_dec(v___x_197_);
v___x_204_ = lean_box(0);
v___y_171_ = v___y_192_;
v___y_172_ = v_extFlat_x3f_193_;
v_prio_x3f_173_ = v___x_204_;
v___y_174_ = v___y_194_;
v___y_175_ = v___y_195_;
goto v___jp_170_;
}
}
v___jp_205_:
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_unsigned_to_nat(2u);
v___x_210_ = l_Lean_Syntax_getArg(v_x_93_, v___x_209_);
v___x_211_ = l_Lean_Syntax_isNone(v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
lean_inc(v___x_210_);
v___x_212_ = l_Lean_Syntax_matchesNull(v___x_210_, v___x_190_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v___x_210_);
lean_dec(v_extIff_x3f_206_);
lean_dec(v_extTk_169_);
lean_dec(v_x_93_);
v___x_213_ = l_Lean_Fmt_Error_partialFormatter;
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___y_208_);
return v___x_214_;
}
else
{
lean_object* v_extFlat_x3f_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_extFlat_x3f_215_ = l_Lean_Syntax_getArg(v___x_210_, v___x_168_);
lean_dec(v___x_210_);
v___x_216_ = ((lean_object*)(l_Lean_Fmt_fmtExtFlat___closed__1));
lean_inc(v_extFlat_x3f_215_);
v___x_217_ = l_Lean_Syntax_isOfKind(v_extFlat_x3f_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_extFlat_x3f_215_);
lean_dec(v_extIff_x3f_206_);
lean_dec(v_extTk_169_);
lean_dec(v_x_93_);
v___x_218_ = l_Lean_Fmt_Error_partialFormatter;
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___y_208_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_extFlat_x3f_215_);
v___y_192_ = v_extIff_x3f_206_;
v_extFlat_x3f_193_ = v___x_220_;
v___y_194_ = v___y_207_;
v___y_195_ = v___y_208_;
goto v___jp_191_;
}
}
}
else
{
lean_object* v___x_221_; 
lean_dec(v___x_210_);
v___x_221_ = lean_box(0);
v___y_192_ = v_extIff_x3f_206_;
v_extFlat_x3f_193_ = v___x_221_;
v___y_194_ = v___y_207_;
v___y_195_ = v___y_208_;
goto v___jp_191_;
}
}
}
v___jp_98_:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Fmt_fmt_x3f(v___y_104_, v___y_99_, v___y_102_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_123_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_a_107_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_123_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_111_ = lean_unsigned_to_nat(4u);
v___x_112_ = lean_mk_empty_array_with_capacity(v___x_111_);
v___x_113_ = lean_array_push(v___x_112_, v___y_101_);
v___x_114_ = lean_array_push(v___x_113_, v___y_100_);
v___x_115_ = lean_array_push(v___x_114_, v___y_103_);
v___x_116_ = lean_array_push(v___x_115_, v_a_106_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_118_, 0, v___x_97_);
lean_ctor_set_uint8(v___x_118_, 1, v___x_117_);
lean_ctor_set_uint8(v___x_118_, 2, v___x_117_);
lean_ctor_set_uint8(v___x_118_, 3, v___x_117_);
v___x_119_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_116_, v___x_118_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_119_);
v___x_121_ = v___x_109_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_a_107_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_dec_ref(v___y_103_);
lean_dec_ref(v___y_101_);
lean_dec_ref(v___y_100_);
return v___x_105_;
}
}
v___jp_124_:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Fmt_fmt_x3f(v___y_130_, v___y_125_, v___y_127_);
if (lean_obj_tag(v___x_131_) == 0)
{
if (lean_obj_tag(v___y_129_) == 0)
{
lean_object* v_a_132_; lean_object* v_a_133_; lean_object* v___x_134_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
v_a_133_ = lean_ctor_get(v___x_131_, 1);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_131_, 2);
v___x_134_ = lean_box(0);
v___y_99_ = v___y_125_;
v___y_100_ = v___y_126_;
v___y_101_ = v___y_128_;
v___y_102_ = v_a_133_;
v___y_103_ = v_a_132_;
v___y_104_ = v___x_134_;
goto v___jp_98_;
}
else
{
lean_object* v_a_135_; lean_object* v_a_136_; lean_object* v_val_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
v_a_135_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_135_);
v_a_136_ = lean_ctor_get(v___x_131_, 1);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_131_, 2);
v_val_137_ = lean_ctor_get(v___y_129_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___y_129_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___y_129_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_val_137_);
lean_dec(v___y_129_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_val_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
v___y_99_ = v___y_125_;
v___y_100_ = v___y_126_;
v___y_101_ = v___y_128_;
v___y_102_ = v_a_136_;
v___y_103_ = v_a_135_;
v___y_104_ = v___x_142_;
goto v___jp_98_;
}
}
}
}
else
{
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec_ref(v___y_126_);
return v___x_131_;
}
}
v___jp_145_:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Fmt_fmt_x3f(v___y_151_, v___y_146_, v___y_150_);
if (lean_obj_tag(v___x_152_) == 0)
{
if (lean_obj_tag(v___y_147_) == 0)
{
lean_object* v_a_153_; lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
v_a_154_ = lean_ctor_get(v___x_152_, 1);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_152_, 2);
v___x_155_ = lean_box(0);
v___y_125_ = v___y_146_;
v___y_126_ = v_a_153_;
v___y_127_ = v_a_154_;
v___y_128_ = v___y_148_;
v___y_129_ = v___y_149_;
v___y_130_ = v___x_155_;
goto v___jp_124_;
}
else
{
lean_object* v_a_156_; lean_object* v_a_157_; lean_object* v_val_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_a_156_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_156_);
v_a_157_ = lean_ctor_get(v___x_152_, 1);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_152_, 2);
v_val_158_ = lean_ctor_get(v___y_147_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___y_147_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___y_147_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_val_158_);
lean_dec(v___y_147_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_val_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
v___y_125_ = v___y_146_;
v___y_126_ = v_a_156_;
v___y_127_ = v_a_157_;
v___y_128_ = v___y_148_;
v___y_129_ = v___y_149_;
v___y_130_ = v___x_163_;
goto v___jp_124_;
}
}
}
}
else
{
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExtAttr___boxed(lean_object* v_x_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Fmt_fmtExtAttr(v_x_234_, v_a_235_, v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1(){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_244_ = l_Lean_Fmt_fmtAttribute;
v___x_245_ = ((lean_object*)(l_Lean_Fmt_fmtExtAttr___closed__1));
v___x_246_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___closed__1));
v___x_247_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExtAttr___boxed), 3, 0);
v___x_248_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_244_, v___x_245_, v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1___boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1();
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticExt(lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; 
v___x_266_ = ((lean_object*)(l_Lean_Fmt_fmtTacticExt___closed__3));
lean_inc(v_x_263_);
v___x_267_ = l_Lean_Syntax_isOfKind(v_x_263_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_x_263_);
v___x_295_ = l_Lean_Fmt_Error_partialFormatter;
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_a_265_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v_extTk_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_colonTk_x3f_302_; lean_object* v_depth_x3f_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v_extTk_298_ = l_Lean_Syntax_getArg(v_x_263_, v___x_297_);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = l_Lean_Syntax_getArg(v_x_263_, v___x_299_);
v___x_336_ = lean_unsigned_to_nat(2u);
v___x_337_ = l_Lean_Syntax_getArg(v_x_263_, v___x_336_);
lean_dec(v_x_263_);
v___x_338_ = l_Lean_Syntax_isNone(v___x_337_);
if (v___x_338_ == 0)
{
uint8_t v___x_339_; 
lean_inc(v___x_337_);
v___x_339_ = l_Lean_Syntax_matchesNull(v___x_337_, v___x_336_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v___x_337_);
lean_dec(v___x_300_);
lean_dec(v_extTk_298_);
v___x_340_ = l_Lean_Fmt_Error_partialFormatter;
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v_a_265_);
return v___x_341_;
}
else
{
lean_object* v_depth_x3f_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_depth_x3f_342_ = l_Lean_Syntax_getArg(v___x_337_, v___x_299_);
v___x_343_ = ((lean_object*)(l_Lean_Fmt_fmtTacticExt___closed__5));
lean_inc(v_depth_x3f_342_);
v___x_344_ = l_Lean_Syntax_isOfKind(v_depth_x3f_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_depth_x3f_342_);
lean_dec(v___x_337_);
lean_dec(v___x_300_);
lean_dec(v_extTk_298_);
v___x_345_ = l_Lean_Fmt_Error_partialFormatter;
v___x_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v_a_265_);
return v___x_346_;
}
else
{
lean_object* v_colonTk_x3f_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_colonTk_x3f_347_ = l_Lean_Syntax_getArg(v___x_337_, v___x_297_);
lean_dec(v___x_337_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v_colonTk_x3f_347_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_depth_x3f_342_);
v_colonTk_x3f_302_ = v___x_348_;
v_depth_x3f_303_ = v___x_349_;
v___y_304_ = v_a_264_;
v___y_305_ = v_a_265_;
goto v___jp_301_;
}
}
}
else
{
lean_object* v___x_350_; 
lean_dec(v___x_337_);
v___x_350_ = lean_box(0);
v_colonTk_x3f_302_ = v___x_350_;
v_depth_x3f_303_ = v___x_350_;
v___y_304_ = v_a_264_;
v___y_305_ = v_a_265_;
goto v___jp_301_;
}
v___jp_301_:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Fmt_fmt(v_extTk_298_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v_a_308_; lean_object* v_pats_309_; lean_object* v___x_310_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
v_a_308_ = lean_ctor_get(v___x_306_, 1);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_306_, 2);
v_pats_309_ = l_Lean_Syntax_getArgs(v___x_300_);
lean_dec(v___x_300_);
v___x_310_ = l_Lean_Fmt_fmtArray___redArg(v_pats_309_, v___y_304_, v_a_308_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v_a_312_; lean_object* v___x_313_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
v_a_312_ = lean_ctor_get(v___x_310_, 1);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_310_, 2);
v___x_313_ = l_Lean_Fmt_fmt_x3f(v_colonTk_x3f_302_, v___y_304_, v_a_312_);
if (lean_obj_tag(v___x_313_) == 0)
{
if (lean_obj_tag(v_depth_x3f_303_) == 0)
{
lean_object* v_a_314_; lean_object* v_a_315_; lean_object* v___x_316_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
v_a_315_ = lean_ctor_get(v___x_313_, 1);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_313_, 2);
v___x_316_ = lean_box(0);
v___y_269_ = v_a_311_;
v___y_270_ = v_a_307_;
v___y_271_ = v_a_315_;
v___y_272_ = v_a_314_;
v___y_273_ = v___y_304_;
v___y_274_ = v___x_316_;
goto v___jp_268_;
}
else
{
lean_object* v_a_317_; lean_object* v_a_318_; lean_object* v_val_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_a_317_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_317_);
v_a_318_ = lean_ctor_get(v___x_313_, 1);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_313_, 2);
v_val_319_ = lean_ctor_get(v_depth_x3f_303_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_depth_x3f_303_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v_depth_x3f_303_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_val_319_);
lean_dec(v_depth_x3f_303_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_val_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v___y_269_ = v_a_311_;
v___y_270_ = v_a_307_;
v___y_271_ = v_a_318_;
v___y_272_ = v_a_317_;
v___y_273_ = v___y_304_;
v___y_274_ = v___x_324_;
goto v___jp_268_;
}
}
}
}
else
{
lean_dec(v_a_311_);
lean_dec(v_a_307_);
lean_dec(v_depth_x3f_303_);
return v___x_313_;
}
}
else
{
lean_object* v_a_327_; lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec(v_a_307_);
lean_dec(v_depth_x3f_303_);
lean_dec(v_colonTk_x3f_302_);
v_a_327_ = lean_ctor_get(v___x_310_, 0);
v_a_328_ = lean_ctor_get(v___x_310_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_310_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_inc(v_a_327_);
lean_dec(v___x_310_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_327_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_dec(v_depth_x3f_303_);
lean_dec(v_colonTk_x3f_302_);
lean_dec(v___x_300_);
return v___x_306_;
}
}
}
v___jp_268_:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Fmt_fmt_x3f(v___y_274_, v___y_273_, v___y_271_);
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
lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_281_ = l_Lean_Fmt_Layouts_fill(v___y_269_);
lean_dec_ref(v___y_269_);
v___x_282_ = 0;
v___x_283_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_283_, 0, v___x_267_);
lean_ctor_set_uint8(v___x_283_, 1, v___x_282_);
lean_ctor_set_uint8(v___x_283_, 2, v___x_267_);
lean_ctor_set_uint8(v___x_283_, 3, v___x_267_);
v___x_284_ = l_Lean_Fmt_Layouts_typeAscription(v___x_281_, v___y_272_, v_a_276_, v___x_283_);
lean_dec_ref_known(v___x_283_, 0);
v___x_285_ = lean_unsigned_to_nat(2u);
v___x_286_ = lean_mk_empty_array_with_capacity(v___x_285_);
v___x_287_ = lean_array_push(v___x_286_, v___y_270_);
v___x_288_ = lean_array_push(v___x_287_, v___x_284_);
v___x_289_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_289_, 0, v___x_267_);
lean_ctor_set_uint8(v___x_289_, 1, v___x_282_);
lean_ctor_set_uint8(v___x_289_, 2, v___x_282_);
lean_ctor_set_uint8(v___x_289_, 3, v___x_282_);
v___x_290_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_288_, v___x_289_);
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
lean_dec_ref(v___y_272_);
lean_dec_ref(v___y_270_);
lean_dec_ref(v___y_269_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticExt___boxed(lean_object* v_x_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Fmt_fmtTacticExt(v_x_351_, v_a_352_, v_a_353_);
lean_dec_ref(v_a_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1(){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_361_ = l_Lean_Fmt_fmtAttribute;
v___x_362_ = ((lean_object*)(l_Lean_Fmt_fmtTacticExt___closed__3));
v___x_363_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___closed__1));
v___x_364_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticExt___boxed), 3, 0);
v___x_365_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_361_, v___x_362_, v___x_363_, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1___boxed(lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1();
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticExt1(lean_object* v_x_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_Fmt_fmtTacticExt1___closed__1));
lean_inc(v_x_375_);
v___x_379_ = l_Lean_Syntax_isOfKind(v_x_375_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_x_375_);
v___x_380_ = l_Lean_Fmt_Error_partialFormatter;
v___x_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_a_377_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; lean_object* v_ext1Tk_383_; lean_object* v___x_384_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v_ext1Tk_383_ = l_Lean_Syntax_getArg(v_x_375_, v___x_382_);
v___x_384_ = l_Lean_Fmt_fmt(v_ext1Tk_383_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_pats_389_; lean_object* v___x_390_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
v_a_386_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_384_, 2);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = l_Lean_Syntax_getArg(v_x_375_, v___x_387_);
lean_dec(v_x_375_);
v_pats_389_ = l_Lean_Syntax_getArgs(v___x_388_);
lean_dec(v___x_388_);
v___x_390_ = l_Lean_Fmt_fmtArray___redArg(v_pats_389_, v_a_376_, v_a_386_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_405_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_a_392_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_405_ == 0)
{
v___x_394_ = v___x_390_;
v_isShared_395_ = v_isSharedCheck_405_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_405_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_396_ = lean_mk_empty_array_with_capacity(v___x_387_);
v___x_397_ = lean_array_push(v___x_396_, v_a_385_);
v___x_398_ = l_Array_append___redArg(v___x_397_, v_a_391_);
lean_dec(v_a_391_);
v___x_399_ = 0;
v___x_400_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_400_, 0, v___x_379_);
lean_ctor_set_uint8(v___x_400_, 1, v___x_399_);
lean_ctor_set_uint8(v___x_400_, 2, v___x_399_);
lean_ctor_set_uint8(v___x_400_, 3, v___x_399_);
v___x_401_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_398_, v___x_400_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_401_);
v___x_403_ = v___x_394_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_a_392_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
else
{
lean_object* v_a_406_; lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_a_385_);
v_a_406_ = lean_ctor_get(v___x_390_, 0);
v_a_407_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_390_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_inc(v_a_406_);
lean_dec(v___x_390_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_406_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_dec(v_x_375_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticExt1___boxed(lean_object* v_x_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Fmt_fmtTacticExt1(v_x_415_, v_a_416_, v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1(){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_425_ = l_Lean_Fmt_fmtAttribute;
v___x_426_ = ((lean_object*)(l_Lean_Fmt_fmtTacticExt1___closed__1));
v___x_427_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___closed__1));
v___x_428_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticExt1___boxed), 3, 0);
v___x_429_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_425_, v___x_426_, v___x_427_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1___boxed(lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1();
return v_res_431_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Ext(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtIff___regBuiltin_Lean_Fmt_fmtExtIff__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtFlat___regBuiltin_Lean_Fmt_fmtExtFlat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtExtAttr___regBuiltin_Lean_Fmt_fmtExtAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt___regBuiltin_Lean_Fmt_fmtTacticExt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Ext_0__Lean_Fmt_fmtTacticExt1___regBuiltin_Lean_Fmt_fmtTacticExt1__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Ext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Ext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Ext(builtin);
}
#ifdef __cplusplus
}
#endif
