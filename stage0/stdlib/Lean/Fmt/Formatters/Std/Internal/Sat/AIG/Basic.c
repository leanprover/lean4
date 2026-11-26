// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Internal.Sat.AIG.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Internal.Sat.AIG.Basic import Init.Data
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_tuple(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sat"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "AIG"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 9, .m_data = "term⟦_,_⟧"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(134, 83, 5, 231, 227, 168, 124, 84)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 208, 173, 190, 196, 161, 76, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__4_value),LEAN_SCALAR_PTR_LITERAL(81, 87, 7, 109, 128, 60, 20, 114)}};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenote___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtAIGDenote"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 65, 19, 4, 82, 250, 107, 88)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 11, .m_data = "term⟦_,_,_⟧"};
static const lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(134, 83, 5, 231, 227, 168, 124, 84)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 208, 173, 190, 196, 161, 76, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 165, 230, 118, 234, 172, 239, 43)}};
static const lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtAIGDenoteEntrypoint"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 99, 3, 171, 10, 234, 228, 207)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenote(lean_object* v_x_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenote___closed__5));
lean_inc(v_x_13_);
v___x_17_ = l_Lean_Syntax_isOfKind(v_x_13_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_x_13_);
v___x_18_ = l_Lean_Fmt_Error_partialFormatter;
v___x_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v_a_15_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; lean_object* v_lbTk_21_; lean_object* v___x_22_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v_lbTk_21_ = l_Lean_Syntax_getArg(v_x_13_, v___x_20_);
v___x_22_ = l_Lean_Fmt_fmt(v_lbTk_21_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v_a_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_commaTk_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_fields_34_; lean_object* v___x_35_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_a_23_);
v_a_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc(v_a_24_);
lean_dec_ref_known(v___x_22_, 2);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = l_Lean_Syntax_getArg(v_x_13_, v___x_25_);
v___x_27_ = lean_unsigned_to_nat(2u);
v_commaTk_28_ = l_Lean_Syntax_getArg(v_x_13_, v___x_27_);
v___x_29_ = lean_unsigned_to_nat(3u);
v___x_30_ = l_Lean_Syntax_getArg(v_x_13_, v___x_29_);
v___x_31_ = lean_mk_empty_array_with_capacity(v___x_29_);
v___x_32_ = lean_array_push(v___x_31_, v___x_26_);
v___x_33_ = lean_array_push(v___x_32_, v_commaTk_28_);
v_fields_34_ = lean_array_push(v___x_33_, v___x_30_);
v___x_35_ = l_Lean_Fmt_fmtTSepArray___redArg(v_fields_34_, v_a_14_, v_a_24_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v_a_37_; lean_object* v___x_38_; lean_object* v_rbTk_39_; lean_object* v___x_40_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_a_36_);
v_a_37_ = lean_ctor_get(v___x_35_, 1);
lean_inc(v_a_37_);
lean_dec_ref_known(v___x_35_, 2);
v___x_38_ = lean_unsigned_to_nat(4u);
v_rbTk_39_ = l_Lean_Syntax_getArg(v_x_13_, v___x_38_);
lean_dec(v_x_13_);
v___x_40_ = l_Lean_Fmt_fmt(v_rbTk_39_, v_a_14_, v_a_37_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_51_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_a_42_ = lean_ctor_get(v___x_40_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_51_ == 0)
{
v___x_44_ = v___x_40_;
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_46_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenote___closed__6));
v___x_47_ = l_Lean_Fmt_Layouts_tuple(v___x_46_, v_a_23_, v_a_36_, v_a_41_);
lean_dec(v_a_36_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_47_);
v___x_49_ = v___x_44_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_a_42_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
else
{
lean_dec(v_a_36_);
lean_dec(v_a_23_);
return v___x_40_;
}
}
else
{
lean_object* v_a_52_; lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
lean_dec(v_a_23_);
lean_dec(v_x_13_);
v_a_52_ = lean_ctor_get(v___x_35_, 0);
v_a_53_ = lean_ctor_get(v___x_35_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_35_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_inc(v_a_52_);
lean_dec(v___x_35_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_52_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
else
{
lean_dec(v_x_13_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenote___boxed(lean_object* v_x_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Fmt_fmtAIGDenote(v_x_61_, v_a_62_, v_a_63_);
lean_dec_ref(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = l_Lean_Fmt_fmtAttribute;
v___x_74_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenote___closed__5));
v___x_75_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3));
v___x_76_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAIGDenote___boxed), 3, 0);
v___x_77_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_73_, v___x_74_, v___x_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1();
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint(lean_object* v_x_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1));
lean_inc(v_x_87_);
v___x_91_ = l_Lean_Syntax_isOfKind(v_x_87_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_x_87_);
v___x_92_ = l_Lean_Fmt_Error_partialFormatter;
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v_a_89_);
return v___x_93_;
}
else
{
lean_object* v___x_94_; lean_object* v_lbTk_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v_lbTk_95_ = l_Lean_Syntax_getArg(v_x_87_, v___x_94_);
v___x_96_ = l_Lean_Fmt_fmt(v_lbTk_95_, v_a_88_, v_a_89_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_comma_u2081Tk_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_comma_u2082Tk_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_fields_114_; lean_object* v___x_115_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_96_, 2);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = l_Lean_Syntax_getArg(v_x_87_, v___x_99_);
v___x_101_ = lean_unsigned_to_nat(2u);
v_comma_u2081Tk_102_ = l_Lean_Syntax_getArg(v_x_87_, v___x_101_);
v___x_103_ = lean_unsigned_to_nat(3u);
v___x_104_ = l_Lean_Syntax_getArg(v_x_87_, v___x_103_);
v___x_105_ = lean_unsigned_to_nat(4u);
v_comma_u2082Tk_106_ = l_Lean_Syntax_getArg(v_x_87_, v___x_105_);
v___x_107_ = lean_unsigned_to_nat(5u);
v___x_108_ = l_Lean_Syntax_getArg(v_x_87_, v___x_107_);
v___x_109_ = lean_mk_empty_array_with_capacity(v___x_107_);
v___x_110_ = lean_array_push(v___x_109_, v___x_100_);
v___x_111_ = lean_array_push(v___x_110_, v_comma_u2081Tk_102_);
v___x_112_ = lean_array_push(v___x_111_, v___x_104_);
v___x_113_ = lean_array_push(v___x_112_, v_comma_u2082Tk_106_);
v_fields_114_ = lean_array_push(v___x_113_, v___x_108_);
v___x_115_ = l_Lean_Fmt_fmtTSepArray___redArg(v_fields_114_, v_a_88_, v_a_98_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v_a_117_; lean_object* v___x_118_; lean_object* v_rbTk_119_; lean_object* v___x_120_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
v_a_117_ = lean_ctor_get(v___x_115_, 1);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_115_, 2);
v___x_118_ = lean_unsigned_to_nat(6u);
v_rbTk_119_ = l_Lean_Syntax_getArg(v_x_87_, v___x_118_);
lean_dec(v_x_87_);
v___x_120_ = l_Lean_Fmt_fmt(v_rbTk_119_, v_a_88_, v_a_117_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_131_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_a_122_ = lean_ctor_get(v___x_120_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_131_ == 0)
{
v___x_124_ = v___x_120_;
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_126_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenote___closed__6));
v___x_127_ = l_Lean_Fmt_Layouts_tuple(v___x_126_, v_a_97_, v_a_116_, v_a_121_);
lean_dec(v_a_116_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_127_);
v___x_129_ = v___x_124_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_a_122_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_dec(v_a_116_);
lean_dec(v_a_97_);
return v___x_120_;
}
}
else
{
lean_object* v_a_132_; lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_dec(v_a_97_);
lean_dec(v_x_87_);
v_a_132_ = lean_ctor_get(v___x_115_, 0);
v_a_133_ = lean_ctor_get(v___x_115_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_115_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_inc(v_a_132_);
lean_dec(v___x_115_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_132_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
else
{
lean_dec(v_x_87_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint___boxed(lean_object* v_x_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Fmt_fmtAIGDenoteEntrypoint(v_x_141_, v_a_142_, v_a_143_);
lean_dec_ref(v_a_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1(){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = l_Lean_Fmt_fmtAttribute;
v___x_152_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1));
v___x_153_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1));
v___x_154_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAIGDenoteEntrypoint___boxed), 3, 0);
v___x_155_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_151_, v___x_152_, v___x_153_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___boxed(lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1();
return v_res_157_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Internal_Sat_AIG_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Internal_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Internal_Sat_AIG_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
