// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Data.Options
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Data.Options meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithDeclModifiers(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_fmtOptionRegistration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtOptionRegistration___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtOptionRegistration___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtOptionRegistration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtOptionRegistration___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "registerBuiltinOption"};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__3_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 128, 225, 170, 242, 224, 12, 82)}};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__8_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtRegisterBuiltinOption"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 99, 229, 204, 6, 244, 112, 221)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "registerOption"};
static const lean_object* l_Lean_Fmt_fmtRegisterOption___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterOption___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterOption___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__3_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 95, 60, 142, 241, 184, 36, 53)}};
static const lean_object* l_Lean_Fmt_fmtRegisterOption___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Fmt_fmtRegisterOption___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterOption___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterOption___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterOption___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__7_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Fmt_fmtRegisterOption___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterOption___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterOption___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtRegisterOption"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterBuiltinOption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 129, 178, 64, 135, 234, 97, 224)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtOptionRegistration(lean_object* v_registerTk_3_, lean_object* v_name_4_, lean_object* v_colonTk_5_, lean_object* v_type_6_, lean_object* v_colonEqTk_7_, lean_object* v_decl_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Fmt_fmt(v_registerTk_3_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_a_12_);
v_a_13_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_a_13_);
lean_dec_ref_known(v___x_11_, 2);
v___x_14_ = l_Lean_Fmt_fmt(v_name_4_, v_a_9_, v_a_13_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_a_15_);
v_a_16_ = lean_ctor_get(v___x_14_, 1);
lean_inc(v_a_16_);
lean_dec_ref_known(v___x_14_, 2);
v___x_17_ = l_Lean_Fmt_fmt(v_colonTk_5_, v_a_9_, v_a_16_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_17_, 2);
v___x_20_ = l_Lean_Fmt_fmt(v_type_6_, v_a_9_, v_a_19_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
v_a_22_ = lean_ctor_get(v___x_20_, 1);
lean_inc(v_a_22_);
lean_dec_ref_known(v___x_20_, 2);
v___x_23_ = l_Lean_Fmt_fmt(v_colonEqTk_7_, v_a_9_, v_a_22_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v_a_25_; lean_object* v___x_26_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
v_a_25_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_a_25_);
lean_dec_ref_known(v___x_23_, 2);
v___x_26_ = l_Lean_Fmt_fmt(v_decl_8_, v_a_9_, v_a_25_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_43_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
v_a_28_ = lean_ctor_get(v___x_26_, 1);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_43_ == 0)
{
v___x_30_ = v___x_26_;
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_inc(v_a_27_);
lean_dec(v___x_26_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_32_ = lean_unsigned_to_nat(2u);
v___x_33_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_34_ = lean_array_push(v___x_33_, v_a_12_);
v___x_35_ = lean_array_push(v___x_34_, v_a_15_);
v___x_36_ = ((lean_object*)(l_Lean_Fmt_fmtOptionRegistration___closed__0));
v___x_37_ = l_Lean_Fmt_Layouts_globalSignature(v___x_35_, v___x_36_, v_a_18_, v_a_21_);
lean_dec_ref(v___x_35_);
v___x_38_ = 0;
v___x_39_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_37_, v_a_24_, v_a_27_, v___x_38_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_39_);
v___x_41_ = v___x_30_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_a_28_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
else
{
lean_dec(v_a_24_);
lean_dec(v_a_21_);
lean_dec(v_a_18_);
lean_dec(v_a_15_);
lean_dec(v_a_12_);
return v___x_26_;
}
}
else
{
lean_dec(v_a_21_);
lean_dec(v_a_18_);
lean_dec(v_a_15_);
lean_dec(v_a_12_);
lean_dec(v_decl_8_);
return v___x_23_;
}
}
else
{
lean_dec(v_a_18_);
lean_dec(v_a_15_);
lean_dec(v_a_12_);
lean_dec(v_decl_8_);
lean_dec(v_colonEqTk_7_);
return v___x_20_;
}
}
else
{
lean_dec(v_a_15_);
lean_dec(v_a_12_);
lean_dec(v_decl_8_);
lean_dec(v_colonEqTk_7_);
lean_dec(v_type_6_);
return v___x_17_;
}
}
else
{
lean_dec(v_a_12_);
lean_dec(v_decl_8_);
lean_dec(v_colonEqTk_7_);
lean_dec(v_type_6_);
lean_dec(v_colonTk_5_);
return v___x_14_;
}
}
else
{
lean_dec(v_decl_8_);
lean_dec(v_colonEqTk_7_);
lean_dec(v_type_6_);
lean_dec(v_colonTk_5_);
lean_dec(v_name_4_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtOptionRegistration___boxed(lean_object* v_registerTk_44_, lean_object* v_name_45_, lean_object* v_colonTk_46_, lean_object* v_type_47_, lean_object* v_colonEqTk_48_, lean_object* v_decl_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Fmt_fmtOptionRegistration(v_registerTk_44_, v_name_45_, v_colonTk_46_, v_type_47_, v_colonEqTk_48_, v_decl_49_, v_a_50_, v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption(lean_object* v_x_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_86_; lean_object* v_visibility_x3f_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5));
lean_inc(v_x_71_);
v___x_119_ = l_Lean_Syntax_isOfKind(v_x_71_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_x_71_);
v___x_120_ = l_Lean_Fmt_Error_partialFormatter;
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_a_73_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v_docComment_x3f_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_136_ = l_Lean_Syntax_getArg(v_x_71_, v___x_122_);
v___x_137_ = l_Lean_Syntax_isNone(v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_136_);
v___x_139_ = l_Lean_Syntax_matchesNull(v___x_136_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v___x_136_);
lean_dec(v_x_71_);
v___x_140_ = l_Lean_Fmt_Error_partialFormatter;
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_a_73_);
return v___x_141_;
}
else
{
lean_object* v_docComment_x3f_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_docComment_x3f_142_ = l_Lean_Syntax_getArg(v___x_136_, v___x_122_);
lean_dec(v___x_136_);
v___x_143_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterBuiltinOption___closed__9));
lean_inc(v_docComment_x3f_142_);
v___x_144_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_docComment_x3f_142_);
lean_dec(v_x_71_);
v___x_145_ = l_Lean_Fmt_Error_partialFormatter;
v___x_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_a_73_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v_docComment_x3f_142_);
v_docComment_x3f_124_ = v___x_147_;
v___y_125_ = v_a_72_;
v___y_126_ = v_a_73_;
goto v___jp_123_;
}
}
}
else
{
lean_object* v___x_148_; 
lean_dec(v___x_136_);
v___x_148_ = lean_box(0);
v_docComment_x3f_124_ = v___x_148_;
v___y_125_ = v_a_72_;
v___y_126_ = v_a_73_;
goto v___jp_123_;
}
v___jp_123_:
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = l_Lean_Syntax_getArg(v_x_71_, v___x_127_);
v___x_129_ = l_Lean_Syntax_isNone(v___x_128_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; 
lean_inc(v___x_128_);
v___x_130_ = l_Lean_Syntax_matchesNull(v___x_128_, v___x_127_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v___x_128_);
lean_dec(v_docComment_x3f_124_);
lean_dec(v_x_71_);
v___x_131_ = l_Lean_Fmt_Error_partialFormatter;
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___y_126_);
return v___x_132_;
}
else
{
lean_object* v_visibility_x3f_133_; lean_object* v___x_134_; 
v_visibility_x3f_133_ = l_Lean_Syntax_getArg(v___x_128_, v___x_122_);
lean_dec(v___x_128_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_visibility_x3f_133_);
v___y_86_ = v_docComment_x3f_124_;
v_visibility_x3f_87_ = v___x_134_;
v___y_88_ = v___y_125_;
v___y_89_ = v___y_126_;
goto v___jp_85_;
}
}
else
{
lean_object* v___x_135_; 
lean_dec(v___x_128_);
v___x_135_ = lean_box(0);
v___y_86_ = v_docComment_x3f_124_;
v_visibility_x3f_87_ = v___x_135_;
v___y_88_ = v___y_125_;
v___y_89_ = v___y_126_;
goto v___jp_85_;
}
}
}
v___jp_74_:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_mk_empty_array_with_capacity(v___x_81_);
v___x_83_ = lean_array_push(v___x_82_, v___y_80_);
v___x_84_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_79_, v___y_77_, v___x_83_, v___y_75_, v___y_76_, v___y_78_);
lean_dec_ref(v___x_83_);
return v___x_84_;
}
v___jp_85_:
{
lean_object* v___x_90_; lean_object* v_name_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_90_ = lean_unsigned_to_nat(3u);
v_name_91_ = l_Lean_Syntax_getArg(v_x_71_, v___x_90_);
v___x_92_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterBuiltinOption___closed__1));
lean_inc(v_name_91_);
v___x_93_ = l_Lean_Syntax_isOfKind(v_name_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_name_91_);
lean_dec(v_visibility_x3f_87_);
lean_dec(v___y_86_);
lean_dec(v_x_71_);
v___x_94_ = l_Lean_Fmt_Error_partialFormatter;
v___x_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___y_89_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; lean_object* v_registerTk_97_; lean_object* v___x_98_; lean_object* v_colonTk_99_; lean_object* v___x_100_; lean_object* v_type_101_; lean_object* v___x_102_; lean_object* v_colonEqTk_103_; lean_object* v___x_104_; lean_object* v_decl_105_; lean_object* v___x_106_; 
v___x_96_ = lean_unsigned_to_nat(2u);
v_registerTk_97_ = l_Lean_Syntax_getArg(v_x_71_, v___x_96_);
v___x_98_ = lean_unsigned_to_nat(4u);
v_colonTk_99_ = l_Lean_Syntax_getArg(v_x_71_, v___x_98_);
v___x_100_ = lean_unsigned_to_nat(5u);
v_type_101_ = l_Lean_Syntax_getArg(v_x_71_, v___x_100_);
v___x_102_ = lean_unsigned_to_nat(6u);
v_colonEqTk_103_ = l_Lean_Syntax_getArg(v_x_71_, v___x_102_);
v___x_104_ = lean_unsigned_to_nat(7u);
v_decl_105_ = l_Lean_Syntax_getArg(v_x_71_, v___x_104_);
lean_dec(v_x_71_);
v___x_106_ = l_Lean_Fmt_fmtOptionRegistration(v_registerTk_97_, v_name_91_, v_colonTk_99_, v_type_101_, v_colonEqTk_103_, v_decl_105_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v___x_109_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
v_a_108_ = lean_ctor_get(v___x_106_, 1);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_106_, 2);
v___x_109_ = lean_box(0);
if (lean_obj_tag(v_visibility_x3f_87_) == 0)
{
v___y_75_ = v_a_107_;
v___y_76_ = v___y_88_;
v___y_77_ = v___x_109_;
v___y_78_ = v_a_108_;
v___y_79_ = v___y_86_;
v___y_80_ = v___x_109_;
goto v___jp_74_;
}
else
{
lean_object* v_val_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_val_110_ = lean_ctor_get(v_visibility_x3f_87_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v_visibility_x3f_87_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v_visibility_x3f_87_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_val_110_);
lean_dec(v_visibility_x3f_87_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_val_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
v___y_75_ = v_a_107_;
v___y_76_ = v___y_88_;
v___y_77_ = v___x_109_;
v___y_78_ = v_a_108_;
v___y_79_ = v___y_86_;
v___y_80_ = v___x_115_;
goto v___jp_74_;
}
}
}
}
else
{
lean_dec(v_visibility_x3f_87_);
lean_dec(v___y_86_);
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterBuiltinOption___boxed(lean_object* v_x_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Fmt_fmtRegisterBuiltinOption(v_x_149_, v_a_150_, v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1(){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_160_ = l_Lean_Fmt_fmtAttribute;
v___x_161_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterBuiltinOption___closed__5));
v___x_162_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___closed__2));
v___x_163_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterBuiltinOption___boxed), 3, 0);
v___x_164_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_160_, v___x_161_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1___boxed(lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1();
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterOption(lean_object* v_x_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterOption___closed__1));
lean_inc(v_x_178_);
v___x_182_ = l_Lean_Syntax_isOfKind(v_x_178_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_x_178_);
v___x_183_ = l_Lean_Fmt_Error_partialFormatter;
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_180_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v_declModifiers_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v_declModifiers_186_ = l_Lean_Syntax_getArg(v_x_178_, v___x_185_);
v___x_187_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterOption___closed__3));
lean_inc(v_declModifiers_186_);
v___x_188_ = l_Lean_Syntax_isOfKind(v_declModifiers_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_declModifiers_186_);
lean_dec(v_x_178_);
v___x_189_ = l_Lean_Fmt_Error_partialFormatter;
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_180_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v_name_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = lean_unsigned_to_nat(2u);
v_name_192_ = l_Lean_Syntax_getArg(v_x_178_, v___x_191_);
v___x_193_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterBuiltinOption___closed__1));
lean_inc(v_name_192_);
v___x_194_ = l_Lean_Syntax_isOfKind(v_name_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_name_192_);
lean_dec(v_declModifiers_186_);
lean_dec(v_x_178_);
v___x_195_ = l_Lean_Fmt_Error_partialFormatter;
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_180_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v_registerTk_198_; lean_object* v___x_199_; lean_object* v_colonTk_200_; lean_object* v___x_201_; lean_object* v_type_202_; lean_object* v___x_203_; lean_object* v_colonEqTk_204_; lean_object* v___x_205_; lean_object* v_decl_206_; lean_object* v___x_207_; 
v___x_197_ = lean_unsigned_to_nat(1u);
v_registerTk_198_ = l_Lean_Syntax_getArg(v_x_178_, v___x_197_);
v___x_199_ = lean_unsigned_to_nat(3u);
v_colonTk_200_ = l_Lean_Syntax_getArg(v_x_178_, v___x_199_);
v___x_201_ = lean_unsigned_to_nat(4u);
v_type_202_ = l_Lean_Syntax_getArg(v_x_178_, v___x_201_);
v___x_203_ = lean_unsigned_to_nat(5u);
v_colonEqTk_204_ = l_Lean_Syntax_getArg(v_x_178_, v___x_203_);
v___x_205_ = lean_unsigned_to_nat(6u);
v_decl_206_ = l_Lean_Syntax_getArg(v_x_178_, v___x_205_);
lean_dec(v_x_178_);
v___x_207_ = l_Lean_Fmt_fmtOptionRegistration(v_registerTk_198_, v_name_192_, v_colonTk_200_, v_type_202_, v_colonEqTk_204_, v_decl_206_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_a_209_; lean_object* v___x_210_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
v_a_209_ = lean_ctor_get(v___x_207_, 1);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_207_, 2);
v___x_210_ = l_Lean_Fmt_fmtDeclWithDeclModifiers(v_declModifiers_186_, v_a_208_, v_a_179_, v_a_209_);
return v___x_210_;
}
else
{
lean_dec(v_declModifiers_186_);
return v___x_207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterOption___boxed(lean_object* v_x_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Fmt_fmtRegisterOption(v_x_211_, v_a_212_, v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1(){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_221_ = l_Lean_Fmt_fmtAttribute;
v___x_222_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterOption___closed__1));
v___x_223_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___closed__1));
v___x_224_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterOption___boxed), 3, 0);
v___x_225_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_221_, v___x_222_, v___x_223_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1___boxed(lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1();
return v_res_227_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Data_Options(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterBuiltinOption___regBuiltin_Lean_Fmt_fmtRegisterBuiltinOption__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Options_0__Lean_Fmt_fmtRegisterOption___regBuiltin_Lean_Fmt_fmtRegisterOption__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Data_Options(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Data_Options(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin);
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
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Data_Options(builtin);
}
#ifdef __cplusplus
}
#endif
