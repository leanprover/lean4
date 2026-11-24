// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Internal.Order.Basic
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Init.NotationExtra meta import Std.Internal.Order.Basic import Init.Data
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
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_quantifierFmtAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_explicitBindersToGroup(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
static const lean_string_object l_Lean_Fmt_fmtIInf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtIInf___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtIInf___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtIInf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Fmt_fmtIInf___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtIInf___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtIInf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term⨅_,_"};
static const lean_object* l_Lean_Fmt_fmtIInf___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtIInf___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtIInf___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtIInf___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIInf___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Fmt_fmtIInf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIInf___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 157, 46, 249, 10, 212, 78, 125)}};
static const lean_object* l_Lean_Fmt_fmtIInf___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtIInf___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtIInf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "explicitBinders"};
static const lean_object* l_Lean_Fmt_fmtIInf___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtIInf___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtIInf___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtIInf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIInf___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 149, 127, 13, 202, 239, 226, 94)}};
static const lean_object* l_Lean_Fmt_fmtIInf___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtIInf___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIInf(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fmtIInf"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 155, 10, 218, 22, 5, 6, 252)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtISup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term⨆_,_"};
static const lean_object* l_Lean_Fmt_fmtISup___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtISup___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtISup___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtISup___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtISup___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Fmt_fmtISup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtISup___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtISup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 181, 131, 200, 113, 90, 194)}};
static const lean_object* l_Lean_Fmt_fmtISup___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtISup___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtISup(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fmtISup"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 167, 230, 203, 92, 106, 162, 205)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLatticeOfProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term⌜_⌝"};
static const lean_object* l_Lean_Fmt_fmtLatticeOfProp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLatticeOfProp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLatticeOfProp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLatticeOfProp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLatticeOfProp___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Fmt_fmtLatticeOfProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLatticeOfProp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLatticeOfProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 16, 241, 71, 126, 146, 187, 11)}};
static const lean_object* l_Lean_Fmt_fmtLatticeOfProp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLatticeOfProp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLatticeOfProp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLatticeOfProp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtLatticeOfProp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIInf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 253, 71, 25, 27, 41, 27, 100)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIInf(lean_object* v_x_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtIInf___closed__3));
lean_inc(v_x_12_);
v___x_14_ = l_Lean_Syntax_isOfKind(v_x_12_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec(v_x_12_);
v___x_15_ = lean_box(0);
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v_bs_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_16_ = lean_unsigned_to_nat(1u);
v_bs_17_ = l_Lean_Syntax_getArg(v_x_12_, v___x_16_);
v___x_18_ = ((lean_object*)(l_Lean_Fmt_fmtIInf___closed__5));
lean_inc(v_bs_17_);
v___x_19_ = l_Lean_Syntax_isOfKind(v_bs_17_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
lean_dec(v_bs_17_);
lean_dec(v_x_12_);
v___x_20_ = lean_box(0);
return v___x_20_;
}
else
{
lean_object* v___x_21_; lean_object* v_iInfTk_22_; lean_object* v___x_23_; lean_object* v_commaTk_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_21_ = lean_unsigned_to_nat(0u);
v_iInfTk_22_ = l_Lean_Syntax_getArg(v_x_12_, v___x_21_);
v___x_23_ = lean_unsigned_to_nat(2u);
v_commaTk_24_ = l_Lean_Syntax_getArg(v_x_12_, v___x_23_);
v___x_25_ = lean_unsigned_to_nat(3u);
v___x_26_ = l_Lean_Syntax_getArg(v_x_12_, v___x_25_);
lean_dec(v_x_12_);
v___x_27_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_17_);
v___x_28_ = lean_mk_empty_array_with_capacity(v___x_16_);
lean_inc_ref(v___x_28_);
v___x_29_ = lean_array_push(v___x_28_, v___x_27_);
v___x_30_ = lean_array_push(v___x_28_, v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_33_, 0, v_iInfTk_22_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
lean_ctor_set(v___x_33_, 3, v___x_32_);
lean_ctor_set(v___x_33_, 4, v_commaTk_24_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_26_);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1(){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_43_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_44_ = ((lean_object*)(l_Lean_Fmt_fmtIInf___closed__3));
v___x_45_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___closed__2));
v___x_46_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtIInf), 1, 0);
v___x_47_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_43_, v___x_44_, v___x_45_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1___boxed(lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1();
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtISup(lean_object* v_x_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_Fmt_fmtISup___closed__1));
lean_inc(v_x_55_);
v___x_57_ = l_Lean_Syntax_isOfKind(v_x_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec(v_x_55_);
v___x_58_ = lean_box(0);
return v___x_58_;
}
else
{
lean_object* v___x_59_; lean_object* v_bs_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_59_ = lean_unsigned_to_nat(1u);
v_bs_60_ = l_Lean_Syntax_getArg(v_x_55_, v___x_59_);
v___x_61_ = ((lean_object*)(l_Lean_Fmt_fmtIInf___closed__5));
lean_inc(v_bs_60_);
v___x_62_ = l_Lean_Syntax_isOfKind(v_bs_60_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec(v_bs_60_);
lean_dec(v_x_55_);
v___x_63_ = lean_box(0);
return v___x_63_;
}
else
{
lean_object* v___x_64_; lean_object* v_iSupTk_65_; lean_object* v___x_66_; lean_object* v_commaTk_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v_iSupTk_65_ = l_Lean_Syntax_getArg(v_x_55_, v___x_64_);
v___x_66_ = lean_unsigned_to_nat(2u);
v_commaTk_67_ = l_Lean_Syntax_getArg(v_x_55_, v___x_66_);
v___x_68_ = lean_unsigned_to_nat(3u);
v___x_69_ = l_Lean_Syntax_getArg(v_x_55_, v___x_68_);
lean_dec(v_x_55_);
v___x_70_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_60_);
v___x_71_ = lean_mk_empty_array_with_capacity(v___x_59_);
lean_inc_ref(v___x_71_);
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
v___x_73_ = lean_array_push(v___x_71_, v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_76_, 0, v_iSupTk_65_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_75_);
lean_ctor_set(v___x_76_, 3, v___x_75_);
lean_ctor_set(v___x_76_, 4, v_commaTk_67_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_69_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1(){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_85_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_86_ = ((lean_object*)(l_Lean_Fmt_fmtISup___closed__1));
v___x_87_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___closed__1));
v___x_88_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtISup), 1, 0);
v___x_89_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_85_, v___x_86_, v___x_87_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1___boxed(lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1();
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLatticeOfProp(lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Fmt_fmtLatticeOfProp___closed__1));
lean_inc(v_x_97_);
v___x_101_ = l_Lean_Syntax_isOfKind(v_x_97_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v_x_97_);
v___x_102_ = l_Lean_Fmt_Error_partialFormatter;
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_a_99_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v_lbTk_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v_lbTk_105_ = l_Lean_Syntax_getArg(v_x_97_, v___x_104_);
v___x_106_ = l_Lean_Fmt_fmt(v_lbTk_105_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
v_a_108_ = lean_ctor_get(v___x_106_, 1);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_106_, 2);
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = l_Lean_Syntax_getArg(v_x_97_, v___x_109_);
v___x_111_ = l_Lean_Fmt_fmt(v___x_110_, v_a_98_, v_a_108_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v_a_113_; lean_object* v___x_114_; lean_object* v_rbTk_115_; lean_object* v___x_116_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
v_a_113_ = lean_ctor_get(v___x_111_, 1);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_111_, 2);
v___x_114_ = lean_unsigned_to_nat(2u);
v_rbTk_115_ = l_Lean_Syntax_getArg(v_x_97_, v___x_114_);
lean_dec(v_x_97_);
v___x_116_ = l_Lean_Fmt_fmt(v_rbTk_115_, v_a_98_, v_a_113_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_a_118_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v___x_116_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = l_Lean_Fmt_Layouts_parens(v_a_107_, v_a_112_, v_a_117_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_a_118_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_dec(v_a_112_);
lean_dec(v_a_107_);
return v___x_116_;
}
}
else
{
lean_dec(v_a_107_);
lean_dec(v_x_97_);
return v___x_111_;
}
}
else
{
lean_dec(v_x_97_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLatticeOfProp___boxed(lean_object* v_x_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Fmt_fmtLatticeOfProp(v_x_127_, v_a_128_, v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1(){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_137_ = l_Lean_Fmt_fmtAttribute;
v___x_138_ = ((lean_object*)(l_Lean_Fmt_fmtLatticeOfProp___closed__1));
v___x_139_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___closed__1));
v___x_140_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLatticeOfProp___boxed), 3, 0);
v___x_141_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_137_, v___x_138_, v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1___boxed(lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1();
return v_res_143_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Internal_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtIInf___regBuiltin_Lean_Fmt_fmtIInf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtISup___regBuiltin_Lean_Fmt_fmtISup__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Internal_Order_Basic_0__Lean_Fmt_fmtLatticeOfProp___regBuiltin_Lean_Fmt_fmtLatticeOfProp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Internal_Order_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Internal_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Std_Internal_Order_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Internal_Order_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Internal_Order_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
