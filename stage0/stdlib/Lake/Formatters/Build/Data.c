// Lean compiler output
// Module: Lake.Formatters.Build.Data
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lake.Build.Data import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclarationSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
static const lean_string_object l_Lake_Formatters_fmtDataTypeDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtDataTypeDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__1_value;
static const lean_array_object l_Lake_Formatters_fmtDataTypeDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__2_value;
static const lean_string_object l_Lake_Formatters_fmtDataTypeDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtDataTypeDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dataTypeDecl"};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtDataTypeDecl___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtDataTypeDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__5_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 208, 230, 96, 184, 13, 30, 26)}};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtDataTypeDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__6_value;
static const lean_string_object l_Lake_Formatters_fmtDataTypeDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__7_value;
static const lean_string_object l_Lake_Formatters_fmtDataTypeDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__8_value;
static const lean_string_object l_Lake_Formatters_fmtDataTypeDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__9_value;
static const lean_ctor_object l_Lake_Formatters_fmtDataTypeDecl___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtDataTypeDecl___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__10_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtDataTypeDecl___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__10_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtDataTypeDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__10_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lake_Formatters_fmtDataTypeDecl___closed__10 = (const lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDataTypeDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDataTypeDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Formatters"};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value;
static const lean_string_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtDataTypeDecl"};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__1_value;
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 72, 251, 122, 252, 99, 166, 215)}};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__2 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtBuiltinFacetCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtinFacetCommand"};
static const lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtBuiltinFacetCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtBuiltinFacetCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtBuiltinFacetCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtBuiltinFacetCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtBuiltinFacetCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 118, 124, 184, 192, 242, 254, 60)}};
static const lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtBuiltinFacetCommand___closed__1_value;
static const lean_array_object l_Lake_Formatters_fmtBuiltinFacetCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtBuiltinFacetCommand___closed__2_value;
static const lean_string_object l_Lake_Formatters_fmtBuiltinFacetCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtBuiltinFacetCommand___closed__3_value;
static const lean_ctor_object l_Lake_Formatters_fmtBuiltinFacetCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtBuiltinFacetCommand___closed__3_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtBuiltinFacetCommand___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtBuiltinFacetCommand"};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 194, 57, 147, 94, 91, 44, 199)}};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___boxed(lean_object*);
static const lean_array_object l_Lake_Formatters_fmtFacetDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Formatters_fmtFacetDataDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtFacetDataDecl___closed__0_value;
static const lean_string_object l_Lake_Formatters_fmtFacetDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "facetDataDecl"};
static const lean_object* l_Lake_Formatters_fmtFacetDataDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtFacetDataDecl___closed__1_value;
static const lean_ctor_object l_Lake_Formatters_fmtFacetDataDecl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtFacetDataDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFacetDataDecl___closed__2_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtFacetDataDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(122, 4, 106, 30, 217, 73, 248, 83)}};
static const lean_object* l_Lake_Formatters_fmtFacetDataDecl___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtFacetDataDecl___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFacetDataDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFacetDataDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtFacetDataDecl"};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 100, 35, 249, 170, 96, 39, 161)}};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtCustomDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "customDataDecl"};
static const lean_object* l_Lake_Formatters_fmtCustomDataDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtCustomDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtCustomDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtCustomDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCustomDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtCustomDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 51, 251, 114, 214, 40, 109, 65)}};
static const lean_object* l_Lake_Formatters_fmtCustomDataDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtCustomDataDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtCustomDataDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtCustomDataDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtCustomDataDecl"};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 4, 162, 20, 191, 28, 157, 241)}};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtPackageDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "packageDataDecl"};
static const lean_object* l_Lake_Formatters_fmtPackageDataDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtPackageDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 160, 98, 6, 154, 122, 231, 28)}};
static const lean_object* l_Lake_Formatters_fmtPackageDataDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtPackageDataDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageDataDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageDataDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtPackageDataDecl"};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 157, 230, 147, 252, 188, 110, 45)}};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtModuleDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "moduleDataDecl"};
static const lean_object* l_Lake_Formatters_fmtModuleDataDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtModuleDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtModuleDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtModuleDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtModuleDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtModuleDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 236, 99, 131, 4, 228, 74, 185)}};
static const lean_object* l_Lake_Formatters_fmtModuleDataDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtModuleDataDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleDataDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleDataDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtModuleDataDecl"};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 237, 15, 43, 11, 5, 44, 200)}};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtLibraryDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "libraryDataDecl"};
static const lean_object* l_Lake_Formatters_fmtLibraryDataDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtLibraryDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtLibraryDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtLibraryDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtLibraryDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtLibraryDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 126, 44, 46, 121, 159, 210, 189)}};
static const lean_object* l_Lake_Formatters_fmtLibraryDataDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtLibraryDataDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLibraryDataDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLibraryDataDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtLibraryDataDecl"};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 187, 255, 179, 70, 187, 6, 92)}};
static const lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDataTypeDecl(lean_object* v_x_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_docComment_x3f_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__5));
lean_inc(v_x_20_);
v___x_51_ = l_Lean_Syntax_isOfKind(v_x_20_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_x_20_);
v___x_52_ = l_Lean_Fmt_Error_partialFormatter;
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v_a_22_);
return v___x_53_;
}
else
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = l_Lean_Syntax_getArg(v_x_20_, v___x_54_);
v___x_56_ = l_Lean_Syntax_isNone(v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_55_);
v___x_58_ = l_Lean_Syntax_matchesNull(v___x_55_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v___x_55_);
lean_dec(v_x_20_);
v___x_59_ = l_Lean_Fmt_Error_partialFormatter;
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v_a_22_);
return v___x_60_;
}
else
{
lean_object* v_docComment_x3f_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v_docComment_x3f_61_ = l_Lean_Syntax_getArg(v___x_55_, v___x_54_);
lean_dec(v___x_55_);
v___x_62_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__10));
lean_inc(v_docComment_x3f_61_);
v___x_63_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_61_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_docComment_x3f_61_);
lean_dec(v_x_20_);
v___x_64_ = l_Lean_Fmt_Error_partialFormatter;
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v_a_22_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; 
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v_docComment_x3f_61_);
v_docComment_x3f_24_ = v___x_66_;
v___y_25_ = v_a_21_;
v___y_26_ = v_a_22_;
goto v___jp_23_;
}
}
}
else
{
lean_object* v___x_67_; 
lean_dec(v___x_55_);
v___x_67_ = lean_box(0);
v_docComment_x3f_24_ = v___x_67_;
v___y_25_ = v_a_21_;
v___y_26_ = v_a_22_;
goto v___jp_23_;
}
}
v___jp_23_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = l_Lean_Syntax_getArg(v_x_20_, v___x_27_);
v___x_29_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__1));
lean_inc(v___x_28_);
v___x_30_ = l_Lean_Syntax_isOfKind(v___x_28_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v___x_28_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
v___x_31_ = l_Lean_Fmt_Error_partialFormatter;
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___y_26_);
return v___x_32_;
}
else
{
lean_object* v___x_33_; lean_object* v_dataTypeTk_34_; lean_object* v___x_35_; lean_object* v_typeAscriptionTk_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_33_ = lean_unsigned_to_nat(1u);
v_dataTypeTk_34_ = l_Lean_Syntax_getArg(v_x_20_, v___x_33_);
v___x_35_ = lean_unsigned_to_nat(3u);
v_typeAscriptionTk_36_ = l_Lean_Syntax_getArg(v_x_20_, v___x_35_);
v___x_37_ = lean_unsigned_to_nat(4u);
v___x_38_ = l_Lean_Syntax_getArg(v_x_20_, v___x_37_);
lean_dec(v_x_20_);
v___x_39_ = lean_mk_empty_array_with_capacity(v___x_33_);
v___x_40_ = lean_array_push(v___x_39_, v_dataTypeTk_34_);
v___x_41_ = lean_box(0);
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_28_);
v___x_43_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__2));
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v_typeAscriptionTk_36_);
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_38_);
v___x_46_ = l_Lean_Fmt_fmtDeclarationSignature(v___x_40_, v___x_41_, v___x_42_, v___x_43_, v___x_44_, v___x_45_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v_a_48_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
v_a_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_46_, 2);
v___x_49_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_24_, v___x_41_, v___x_43_, v_a_47_, v___y_25_, v_a_48_);
return v___x_49_;
}
else
{
lean_dec(v_docComment_x3f_24_);
return v___x_46_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDataTypeDecl___boxed(lean_object* v_x_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lake_Formatters_fmtDataTypeDecl(v_x_68_, v_a_69_, v_a_70_);
lean_dec_ref(v_a_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1(){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = l_Lean_Fmt_fmtAttribute;
v___x_80_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__5));
v___x_81_ = ((lean_object*)(l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___closed__2));
v___x_82_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtDataTypeDecl___boxed), 3, 0);
v___x_83_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_79_, v___x_80_, v___x_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1___boxed(lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand(lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lake_Formatters_fmtBuiltinFacetCommand___closed__1));
lean_inc(v_x_95_);
v___x_99_ = l_Lean_Syntax_isOfKind(v_x_95_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_x_95_);
v___x_100_ = l_Lean_Fmt_Error_partialFormatter;
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_a_97_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v___y_115_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v_id_x3f_156_; lean_object* v_atTk_x3f_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v_docComment_x3f_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_215_ = l_Lean_Syntax_getArg(v_x_95_, v___x_102_);
v___x_216_ = l_Lean_Syntax_isNone(v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_215_);
v___x_218_ = l_Lean_Syntax_matchesNull(v___x_215_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v___x_215_);
lean_dec(v_x_95_);
v___x_219_ = l_Lean_Fmt_Error_partialFormatter;
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_a_97_);
return v___x_220_;
}
else
{
lean_object* v_docComment_x3f_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_docComment_x3f_221_ = l_Lean_Syntax_getArg(v___x_215_, v___x_102_);
lean_dec(v___x_215_);
v___x_222_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__10));
lean_inc(v_docComment_x3f_221_);
v___x_223_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v_docComment_x3f_221_);
lean_dec(v_x_95_);
v___x_224_ = l_Lean_Fmt_Error_partialFormatter;
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v_a_97_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; 
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v_docComment_x3f_221_);
v_docComment_x3f_190_ = v___x_226_;
v___y_191_ = v_a_96_;
v___y_192_ = v_a_97_;
goto v___jp_189_;
}
}
}
else
{
lean_object* v___x_227_; 
lean_dec(v___x_215_);
v___x_227_ = lean_box(0);
v_docComment_x3f_190_ = v___x_227_;
v___y_191_ = v_a_96_;
v___y_192_ = v_a_97_;
goto v___jp_189_;
}
v___jp_103_:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Fmt_fmt_x3f(v___y_115_, v___y_104_, v___y_110_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v_a_118_; lean_object* v___x_119_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
v_a_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_116_, 2);
v___x_119_ = l_Lean_Fmt_fmt_x3f(v___y_107_, v___y_104_, v_a_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v_a_121_; lean_object* v___x_122_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
v_a_121_ = lean_ctor_get(v___x_119_, 1);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_119_, 2);
v___x_122_ = l_Lean_Fmt_fmt(v___y_105_, v___y_104_, v_a_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v_a_124_; lean_object* v___x_125_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
v_a_124_ = lean_ctor_get(v___x_122_, 1);
lean_inc(v_a_124_);
lean_dec_ref_known(v___x_122_, 2);
v___x_125_ = l_Lean_Fmt_fmt(v___y_108_, v___y_104_, v_a_124_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_126_);
v_a_127_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_a_127_);
lean_dec_ref_known(v___x_125_, 2);
v___x_128_ = l_Lean_Fmt_fmt(v___y_113_, v___y_104_, v_a_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v_a_130_; lean_object* v___x_131_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
v_a_130_ = lean_ctor_get(v___x_128_, 1);
lean_inc(v_a_130_);
lean_dec_ref_known(v___x_128_, 2);
v___x_131_ = l_Lean_Fmt_fmt(v___y_114_, v___y_104_, v_a_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v_a_133_; lean_object* v___x_134_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
v_a_133_ = lean_ctor_get(v___x_131_, 1);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_131_, 2);
v___x_134_ = l_Lean_Fmt_fmt(v___y_106_, v___y_104_, v_a_133_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
v_a_136_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_134_, 2);
v___x_137_ = lean_mk_empty_array_with_capacity(v___y_112_);
v___x_138_ = lean_array_push(v___x_137_, v_a_117_);
v___x_139_ = lean_array_push(v___x_138_, v_a_120_);
v___x_140_ = lean_array_push(v___x_139_, v_a_123_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_142_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_142_, 1, v___x_141_);
lean_ctor_set_uint8(v___x_142_, 2, v___x_99_);
lean_ctor_set_uint8(v___x_142_, 3, v___x_99_);
v___x_143_ = l_Lean_Fmt_Layouts_infixOperator(v___x_140_, v___x_142_);
lean_dec_ref_known(v___x_142_, 0);
v___x_144_ = lean_unsigned_to_nat(2u);
v___x_145_ = lean_mk_empty_array_with_capacity(v___x_144_);
v___x_146_ = lean_array_push(v___x_145_, v___y_111_);
v___x_147_ = lean_array_push(v___x_146_, v___x_143_);
v___x_148_ = ((lean_object*)(l_Lake_Formatters_fmtBuiltinFacetCommand___closed__2));
v___x_149_ = l_Lean_Fmt_Layouts_globalSignature(v___x_147_, v___x_148_, v_a_126_, v_a_129_);
lean_dec_ref(v___x_147_);
v___x_150_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_149_, v_a_132_, v_a_135_, v___x_141_);
v___x_151_ = lean_box(0);
v___x_152_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_109_, v___x_151_, v___x_148_, v___x_150_, v___y_104_, v_a_136_);
return v___x_152_;
}
else
{
lean_dec(v_a_132_);
lean_dec(v_a_129_);
lean_dec(v_a_126_);
lean_dec(v_a_123_);
lean_dec(v_a_120_);
lean_dec(v_a_117_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_109_);
return v___x_134_;
}
}
else
{
lean_dec(v_a_129_);
lean_dec(v_a_126_);
lean_dec(v_a_123_);
lean_dec(v_a_120_);
lean_dec(v_a_117_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_109_);
lean_dec(v___y_106_);
return v___x_131_;
}
}
else
{
lean_dec(v_a_126_);
lean_dec(v_a_123_);
lean_dec(v_a_120_);
lean_dec(v_a_117_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_109_);
lean_dec(v___y_106_);
return v___x_128_;
}
}
else
{
lean_dec(v_a_123_);
lean_dec(v_a_120_);
lean_dec(v_a_117_);
lean_dec(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_109_);
lean_dec(v___y_106_);
return v___x_125_;
}
}
else
{
lean_dec(v_a_120_);
lean_dec(v_a_117_);
lean_dec(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
lean_dec(v___y_106_);
return v___x_122_;
}
}
else
{
lean_dec(v_a_117_);
lean_dec(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
return v___x_119_;
}
}
else
{
lean_dec(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
lean_dec(v___y_107_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
return v___x_116_;
}
}
v___jp_153_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_160_ = lean_unsigned_to_nat(3u);
v___x_161_ = l_Lean_Syntax_getArg(v_x_95_, v___x_160_);
v___x_162_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__1));
lean_inc(v___x_161_);
v___x_163_ = l_Lean_Syntax_isOfKind(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v___x_161_);
lean_dec(v_atTk_x3f_157_);
lean_dec(v_id_x3f_156_);
lean_dec(v___y_155_);
lean_dec(v___y_154_);
lean_dec(v_x_95_);
v___x_164_ = l_Lean_Fmt_Error_partialFormatter;
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___y_159_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_unsigned_to_nat(5u);
v___x_167_ = l_Lean_Syntax_getArg(v_x_95_, v___x_166_);
lean_inc(v___x_167_);
v___x_168_ = l_Lean_Syntax_isOfKind(v___x_167_, v___x_162_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v___x_167_);
lean_dec(v___x_161_);
lean_dec(v_atTk_x3f_157_);
lean_dec(v_id_x3f_156_);
lean_dec(v___y_155_);
lean_dec(v___y_154_);
lean_dec(v_x_95_);
v___x_169_ = l_Lean_Fmt_Error_partialFormatter;
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___y_159_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Fmt_fmt(v___y_155_, v___y_158_, v___y_159_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v_typeAscriptionTk_175_; lean_object* v___x_176_; lean_object* v_arrowTk_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
v_a_173_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_171_, 2);
v___x_174_ = lean_unsigned_to_nat(4u);
v_typeAscriptionTk_175_ = l_Lean_Syntax_getArg(v_x_95_, v___x_174_);
v___x_176_ = lean_unsigned_to_nat(6u);
v_arrowTk_177_ = l_Lean_Syntax_getArg(v_x_95_, v___x_176_);
v___x_178_ = lean_unsigned_to_nat(7u);
v___x_179_ = l_Lean_Syntax_getArg(v_x_95_, v___x_178_);
lean_dec(v_x_95_);
if (lean_obj_tag(v_id_x3f_156_) == 0)
{
lean_object* v___x_180_; 
v___x_180_ = lean_box(0);
v___y_104_ = v___y_158_;
v___y_105_ = v___x_161_;
v___y_106_ = v___x_179_;
v___y_107_ = v_atTk_x3f_157_;
v___y_108_ = v_typeAscriptionTk_175_;
v___y_109_ = v___y_154_;
v___y_110_ = v_a_173_;
v___y_111_ = v_a_172_;
v___y_112_ = v___x_160_;
v___y_113_ = v___x_167_;
v___y_114_ = v_arrowTk_177_;
v___y_115_ = v___x_180_;
goto v___jp_103_;
}
else
{
lean_object* v_val_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_val_181_ = lean_ctor_get(v_id_x3f_156_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v_id_x3f_156_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v_id_x3f_156_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_val_181_);
lean_dec(v_id_x3f_156_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_val_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
v___y_104_ = v___y_158_;
v___y_105_ = v___x_161_;
v___y_106_ = v___x_179_;
v___y_107_ = v_atTk_x3f_157_;
v___y_108_ = v_typeAscriptionTk_175_;
v___y_109_ = v___y_154_;
v___y_110_ = v_a_173_;
v___y_111_ = v_a_172_;
v___y_112_ = v___x_160_;
v___y_113_ = v___x_167_;
v___y_114_ = v_arrowTk_177_;
v___y_115_ = v___x_186_;
goto v___jp_103_;
}
}
}
}
else
{
lean_dec(v___x_167_);
lean_dec(v___x_161_);
lean_dec(v_atTk_x3f_157_);
lean_dec(v_id_x3f_156_);
lean_dec(v___y_154_);
lean_dec(v_x_95_);
return v___x_171_;
}
}
}
}
v___jp_189_:
{
lean_object* v___x_193_; lean_object* v_builtinFacetTk_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v_builtinFacetTk_194_ = l_Lean_Syntax_getArg(v_x_95_, v___x_193_);
v___x_195_ = lean_unsigned_to_nat(2u);
v___x_196_ = l_Lean_Syntax_getArg(v_x_95_, v___x_195_);
v___x_197_ = l_Lean_Syntax_isNone(v___x_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
lean_inc(v___x_196_);
v___x_198_ = l_Lean_Syntax_matchesNull(v___x_196_, v___x_193_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v___x_196_);
lean_dec(v_builtinFacetTk_194_);
lean_dec(v_docComment_x3f_190_);
lean_dec(v_x_95_);
v___x_199_ = l_Lean_Fmt_Error_partialFormatter;
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___y_192_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_201_ = l_Lean_Syntax_getArg(v___x_196_, v___x_102_);
lean_dec(v___x_196_);
v___x_202_ = ((lean_object*)(l_Lake_Formatters_fmtBuiltinFacetCommand___closed__4));
lean_inc(v___x_201_);
v___x_203_ = l_Lean_Syntax_isOfKind(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v___x_201_);
lean_dec(v_builtinFacetTk_194_);
lean_dec(v_docComment_x3f_190_);
lean_dec(v_x_95_);
v___x_204_ = l_Lean_Fmt_Error_partialFormatter;
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___y_192_);
return v___x_205_;
}
else
{
lean_object* v_id_x3f_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_id_x3f_206_ = l_Lean_Syntax_getArg(v___x_201_, v___x_102_);
v___x_207_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__1));
lean_inc(v_id_x3f_206_);
v___x_208_ = l_Lean_Syntax_isOfKind(v_id_x3f_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_id_x3f_206_);
lean_dec(v___x_201_);
lean_dec(v_builtinFacetTk_194_);
lean_dec(v_docComment_x3f_190_);
lean_dec(v_x_95_);
v___x_209_ = l_Lean_Fmt_Error_partialFormatter;
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___y_192_);
return v___x_210_;
}
else
{
lean_object* v_atTk_x3f_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_atTk_x3f_211_ = l_Lean_Syntax_getArg(v___x_201_, v___x_193_);
lean_dec(v___x_201_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v_id_x3f_206_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v_atTk_x3f_211_);
v___y_154_ = v_docComment_x3f_190_;
v___y_155_ = v_builtinFacetTk_194_;
v_id_x3f_156_ = v___x_212_;
v_atTk_x3f_157_ = v___x_213_;
v___y_158_ = v___y_191_;
v___y_159_ = v___y_192_;
goto v___jp_153_;
}
}
}
}
else
{
lean_object* v___x_214_; 
lean_dec(v___x_196_);
v___x_214_ = lean_box(0);
v___y_154_ = v_docComment_x3f_190_;
v___y_155_ = v_builtinFacetTk_194_;
v_id_x3f_156_ = v___x_214_;
v_atTk_x3f_157_ = v___x_214_;
v___y_158_ = v___y_191_;
v___y_159_ = v___y_192_;
goto v___jp_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtBuiltinFacetCommand___boxed(lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_Formatters_fmtBuiltinFacetCommand(v_x_228_, v_a_229_, v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1(){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_238_ = l_Lean_Fmt_fmtAttribute;
v___x_239_ = ((lean_object*)(l_Lake_Formatters_fmtBuiltinFacetCommand___closed__1));
v___x_240_ = ((lean_object*)(l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___closed__1));
v___x_241_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtBuiltinFacetCommand___boxed), 3, 0);
v___x_242_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_238_, v___x_239_, v___x_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1___boxed(lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1();
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFacetDataDecl(lean_object* v_x_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_docComment_x3f_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = ((lean_object*)(l_Lake_Formatters_fmtFacetDataDecl___closed__2));
lean_inc(v_x_251_);
v___x_288_ = l_Lean_Syntax_isOfKind(v_x_251_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_x_251_);
v___x_289_ = l_Lean_Fmt_Error_partialFormatter;
v___x_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_a_253_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Lean_Syntax_getArg(v_x_251_, v___x_291_);
v___x_293_ = l_Lean_Syntax_isNone(v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_292_);
v___x_295_ = l_Lean_Syntax_matchesNull(v___x_292_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v___x_292_);
lean_dec(v_x_251_);
v___x_296_ = l_Lean_Fmt_Error_partialFormatter;
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_253_);
return v___x_297_;
}
else
{
lean_object* v_docComment_x3f_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_docComment_x3f_298_ = l_Lean_Syntax_getArg(v___x_292_, v___x_291_);
lean_dec(v___x_292_);
v___x_299_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__10));
lean_inc(v_docComment_x3f_298_);
v___x_300_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_docComment_x3f_298_);
lean_dec(v_x_251_);
v___x_301_ = l_Lean_Fmt_Error_partialFormatter;
v___x_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v_a_253_);
return v___x_302_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v_docComment_x3f_298_);
v_docComment_x3f_255_ = v___x_303_;
v___y_256_ = v_a_252_;
v___y_257_ = v_a_253_;
goto v___jp_254_;
}
}
}
else
{
lean_object* v___x_304_; 
lean_dec(v___x_292_);
v___x_304_ = lean_box(0);
v_docComment_x3f_255_ = v___x_304_;
v___y_256_ = v_a_252_;
v___y_257_ = v_a_253_;
goto v___jp_254_;
}
}
v___jp_254_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_258_ = lean_unsigned_to_nat(2u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_251_, v___x_258_);
v___x_260_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__1));
lean_inc(v___x_259_);
v___x_261_ = l_Lean_Syntax_isOfKind(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v___x_259_);
lean_dec(v_docComment_x3f_255_);
lean_dec(v_x_251_);
v___x_262_ = l_Lean_Fmt_Error_partialFormatter;
v___x_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___y_257_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_unsigned_to_nat(3u);
v___x_265_ = l_Lean_Syntax_getArg(v_x_251_, v___x_264_);
lean_inc(v___x_265_);
v___x_266_ = l_Lean_Syntax_isOfKind(v___x_265_, v___x_260_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v___x_265_);
lean_dec(v___x_259_);
lean_dec(v_docComment_x3f_255_);
lean_dec(v_x_251_);
v___x_267_ = l_Lean_Fmt_Error_partialFormatter;
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___y_257_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v_facetDataTk_270_; lean_object* v___x_271_; lean_object* v_typeAscriptionTk_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v_facetDataTk_270_ = l_Lean_Syntax_getArg(v_x_251_, v___x_269_);
v___x_271_ = lean_unsigned_to_nat(4u);
v_typeAscriptionTk_272_ = l_Lean_Syntax_getArg(v_x_251_, v___x_271_);
v___x_273_ = lean_unsigned_to_nat(5u);
v___x_274_ = l_Lean_Syntax_getArg(v_x_251_, v___x_273_);
lean_dec(v_x_251_);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_269_);
lean_inc_ref(v___x_275_);
v___x_276_ = lean_array_push(v___x_275_, v_facetDataTk_270_);
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_259_);
v___x_279_ = lean_array_push(v___x_275_, v___x_265_);
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v_typeAscriptionTk_272_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_274_);
v___x_282_ = l_Lean_Fmt_fmtDeclarationSignature(v___x_276_, v___x_277_, v___x_278_, v___x_279_, v___x_280_, v___x_281_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
v_a_284_ = lean_ctor_get(v___x_282_, 1);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_282_, 2);
v___x_285_ = ((lean_object*)(l_Lake_Formatters_fmtFacetDataDecl___closed__0));
v___x_286_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_255_, v___x_277_, v___x_285_, v_a_283_, v___y_256_, v_a_284_);
return v___x_286_;
}
else
{
lean_dec(v_docComment_x3f_255_);
return v___x_282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFacetDataDecl___boxed(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lake_Formatters_fmtFacetDataDecl(v_x_305_, v_a_306_, v_a_307_);
lean_dec_ref(v_a_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1(){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_315_ = l_Lean_Fmt_fmtAttribute;
v___x_316_ = ((lean_object*)(l_Lake_Formatters_fmtFacetDataDecl___closed__2));
v___x_317_ = ((lean_object*)(l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___closed__1));
v___x_318_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtFacetDataDecl___boxed), 3, 0);
v___x_319_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_315_, v___x_316_, v___x_317_, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1___boxed(lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtCustomDataDecl(lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_docComment_x3f_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lake_Formatters_fmtCustomDataDecl___closed__1));
lean_inc(v_x_326_);
v___x_363_ = l_Lean_Syntax_isOfKind(v_x_326_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_x_326_);
v___x_364_ = l_Lean_Fmt_Error_partialFormatter;
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_a_328_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = l_Lean_Syntax_getArg(v_x_326_, v___x_366_);
v___x_368_ = l_Lean_Syntax_isNone(v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_367_);
v___x_370_ = l_Lean_Syntax_matchesNull(v___x_367_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v___x_367_);
lean_dec(v_x_326_);
v___x_371_ = l_Lean_Fmt_Error_partialFormatter;
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_a_328_);
return v___x_372_;
}
else
{
lean_object* v_docComment_x3f_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_docComment_x3f_373_ = l_Lean_Syntax_getArg(v___x_367_, v___x_366_);
lean_dec(v___x_367_);
v___x_374_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__10));
lean_inc(v_docComment_x3f_373_);
v___x_375_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_373_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_docComment_x3f_373_);
lean_dec(v_x_326_);
v___x_376_ = l_Lean_Fmt_Error_partialFormatter;
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_a_328_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v_docComment_x3f_373_);
v_docComment_x3f_330_ = v___x_378_;
v___y_331_ = v_a_327_;
v___y_332_ = v_a_328_;
goto v___jp_329_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v___x_367_);
v___x_379_ = lean_box(0);
v_docComment_x3f_330_ = v___x_379_;
v___y_331_ = v_a_327_;
v___y_332_ = v_a_328_;
goto v___jp_329_;
}
}
v___jp_329_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = l_Lean_Syntax_getArg(v_x_326_, v___x_333_);
v___x_335_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__1));
lean_inc(v___x_334_);
v___x_336_ = l_Lean_Syntax_isOfKind(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v___x_334_);
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
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_unsigned_to_nat(3u);
v___x_340_ = l_Lean_Syntax_getArg(v_x_326_, v___x_339_);
lean_inc(v___x_340_);
v___x_341_ = l_Lean_Syntax_isOfKind(v___x_340_, v___x_335_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v___x_340_);
lean_dec(v___x_334_);
lean_dec(v_docComment_x3f_330_);
lean_dec(v_x_326_);
v___x_342_ = l_Lean_Fmt_Error_partialFormatter;
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___y_332_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v_customDataTk_345_; lean_object* v___x_346_; lean_object* v_typeAscriptionTk_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v_customDataTk_345_ = l_Lean_Syntax_getArg(v_x_326_, v___x_344_);
v___x_346_ = lean_unsigned_to_nat(4u);
v_typeAscriptionTk_347_ = l_Lean_Syntax_getArg(v_x_326_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(5u);
v___x_349_ = l_Lean_Syntax_getArg(v_x_326_, v___x_348_);
lean_dec(v_x_326_);
v___x_350_ = lean_mk_empty_array_with_capacity(v___x_344_);
lean_inc_ref(v___x_350_);
v___x_351_ = lean_array_push(v___x_350_, v_customDataTk_345_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_334_);
v___x_354_ = lean_array_push(v___x_350_, v___x_340_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_typeAscriptionTk_347_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_349_);
v___x_357_ = l_Lean_Fmt_fmtDeclarationSignature(v___x_351_, v___x_352_, v___x_353_, v___x_354_, v___x_355_, v___x_356_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v_a_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
v_a_359_ = lean_ctor_get(v___x_357_, 1);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_357_, 2);
v___x_360_ = ((lean_object*)(l_Lake_Formatters_fmtFacetDataDecl___closed__0));
v___x_361_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_330_, v___x_352_, v___x_360_, v_a_358_, v___y_331_, v_a_359_);
return v___x_361_;
}
else
{
lean_dec(v_docComment_x3f_330_);
return v___x_357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtCustomDataDecl___boxed(lean_object* v_x_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lake_Formatters_fmtCustomDataDecl(v_x_380_, v_a_381_, v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1(){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_390_ = l_Lean_Fmt_fmtAttribute;
v___x_391_ = ((lean_object*)(l_Lake_Formatters_fmtCustomDataDecl___closed__1));
v___x_392_ = ((lean_object*)(l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___closed__1));
v___x_393_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtCustomDataDecl___boxed), 3, 0);
v___x_394_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_390_, v___x_391_, v___x_392_, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1___boxed(lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1();
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageDataDecl(lean_object* v_x_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_docComment_x3f_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lake_Formatters_fmtPackageDataDecl___closed__1));
lean_inc(v_x_401_);
v___x_432_ = l_Lean_Syntax_isOfKind(v_x_401_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_x_401_);
v___x_433_ = l_Lean_Fmt_Error_partialFormatter;
v___x_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_a_403_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = l_Lean_Syntax_getArg(v_x_401_, v___x_435_);
v___x_437_ = l_Lean_Syntax_isNone(v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_436_);
v___x_439_ = l_Lean_Syntax_matchesNull(v___x_436_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v___x_436_);
lean_dec(v_x_401_);
v___x_440_ = l_Lean_Fmt_Error_partialFormatter;
v___x_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v_a_403_);
return v___x_441_;
}
else
{
lean_object* v_docComment_x3f_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_docComment_x3f_442_ = l_Lean_Syntax_getArg(v___x_436_, v___x_435_);
lean_dec(v___x_436_);
v___x_443_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__10));
lean_inc(v_docComment_x3f_442_);
v___x_444_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_docComment_x3f_442_);
lean_dec(v_x_401_);
v___x_445_ = l_Lean_Fmt_Error_partialFormatter;
v___x_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v_a_403_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_docComment_x3f_442_);
v_docComment_x3f_405_ = v___x_447_;
v___y_406_ = v_a_402_;
v___y_407_ = v_a_403_;
goto v___jp_404_;
}
}
}
else
{
lean_object* v___x_448_; 
lean_dec(v___x_436_);
v___x_448_ = lean_box(0);
v_docComment_x3f_405_ = v___x_448_;
v___y_406_ = v_a_402_;
v___y_407_ = v_a_403_;
goto v___jp_404_;
}
}
v___jp_404_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_408_ = lean_unsigned_to_nat(2u);
v___x_409_ = l_Lean_Syntax_getArg(v_x_401_, v___x_408_);
v___x_410_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__1));
lean_inc(v___x_409_);
v___x_411_ = l_Lean_Syntax_isOfKind(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v___x_409_);
lean_dec(v_docComment_x3f_405_);
lean_dec(v_x_401_);
v___x_412_ = l_Lean_Fmt_Error_partialFormatter;
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___y_407_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v_packageDataTk_415_; lean_object* v___x_416_; lean_object* v_typeAscriptionTk_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v_packageDataTk_415_ = l_Lean_Syntax_getArg(v_x_401_, v___x_414_);
v___x_416_ = lean_unsigned_to_nat(3u);
v_typeAscriptionTk_417_ = l_Lean_Syntax_getArg(v_x_401_, v___x_416_);
v___x_418_ = lean_unsigned_to_nat(4u);
v___x_419_ = l_Lean_Syntax_getArg(v_x_401_, v___x_418_);
lean_dec(v_x_401_);
v___x_420_ = lean_mk_empty_array_with_capacity(v___x_414_);
v___x_421_ = lean_array_push(v___x_420_, v_packageDataTk_415_);
v___x_422_ = lean_box(0);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_409_);
v___x_424_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__2));
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v_typeAscriptionTk_417_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_419_);
v___x_427_ = l_Lean_Fmt_fmtDeclarationSignature(v___x_421_, v___x_422_, v___x_423_, v___x_424_, v___x_425_, v___x_426_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v_a_429_; lean_object* v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
v_a_429_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_427_, 2);
v___x_430_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_405_, v___x_422_, v___x_424_, v_a_428_, v___y_406_, v_a_429_);
return v___x_430_;
}
else
{
lean_dec(v_docComment_x3f_405_);
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageDataDecl___boxed(lean_object* v_x_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_Formatters_fmtPackageDataDecl(v_x_449_, v_a_450_, v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_459_ = l_Lean_Fmt_fmtAttribute;
v___x_460_ = ((lean_object*)(l_Lake_Formatters_fmtPackageDataDecl___closed__1));
v___x_461_ = ((lean_object*)(l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___closed__1));
v___x_462_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtPackageDataDecl___boxed), 3, 0);
v___x_463_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_459_, v___x_460_, v___x_461_, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1___boxed(lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1();
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleDataDecl(lean_object* v_x_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_docComment_x3f_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lake_Formatters_fmtModuleDataDecl___closed__1));
lean_inc(v_x_470_);
v___x_501_ = l_Lean_Syntax_isOfKind(v_x_470_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_x_470_);
v___x_502_ = l_Lean_Fmt_Error_partialFormatter;
v___x_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_a_472_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = l_Lean_Syntax_getArg(v_x_470_, v___x_504_);
v___x_506_ = l_Lean_Syntax_isNone(v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_505_);
v___x_508_ = l_Lean_Syntax_matchesNull(v___x_505_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v___x_505_);
lean_dec(v_x_470_);
v___x_509_ = l_Lean_Fmt_Error_partialFormatter;
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_a_472_);
return v___x_510_;
}
else
{
lean_object* v_docComment_x3f_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_docComment_x3f_511_ = l_Lean_Syntax_getArg(v___x_505_, v___x_504_);
lean_dec(v___x_505_);
v___x_512_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__10));
lean_inc(v_docComment_x3f_511_);
v___x_513_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_docComment_x3f_511_);
lean_dec(v_x_470_);
v___x_514_ = l_Lean_Fmt_Error_partialFormatter;
v___x_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_a_472_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_docComment_x3f_511_);
v_docComment_x3f_474_ = v___x_516_;
v___y_475_ = v_a_471_;
v___y_476_ = v_a_472_;
goto v___jp_473_;
}
}
}
else
{
lean_object* v___x_517_; 
lean_dec(v___x_505_);
v___x_517_ = lean_box(0);
v_docComment_x3f_474_ = v___x_517_;
v___y_475_ = v_a_471_;
v___y_476_ = v_a_472_;
goto v___jp_473_;
}
}
v___jp_473_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_477_ = lean_unsigned_to_nat(2u);
v___x_478_ = l_Lean_Syntax_getArg(v_x_470_, v___x_477_);
v___x_479_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__1));
lean_inc(v___x_478_);
v___x_480_ = l_Lean_Syntax_isOfKind(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v___x_478_);
lean_dec(v_docComment_x3f_474_);
lean_dec(v_x_470_);
v___x_481_ = l_Lean_Fmt_Error_partialFormatter;
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___y_476_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v_moduleDataTk_484_; lean_object* v___x_485_; lean_object* v_typeAscriptionTk_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v_moduleDataTk_484_ = l_Lean_Syntax_getArg(v_x_470_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(3u);
v_typeAscriptionTk_486_ = l_Lean_Syntax_getArg(v_x_470_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(4u);
v___x_488_ = l_Lean_Syntax_getArg(v_x_470_, v___x_487_);
lean_dec(v_x_470_);
v___x_489_ = lean_mk_empty_array_with_capacity(v___x_483_);
v___x_490_ = lean_array_push(v___x_489_, v_moduleDataTk_484_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_478_);
v___x_493_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__2));
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_typeAscriptionTk_486_);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_488_);
v___x_496_ = l_Lean_Fmt_fmtDeclarationSignature(v___x_490_, v___x_491_, v___x_492_, v___x_493_, v___x_494_, v___x_495_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v_a_498_; lean_object* v___x_499_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
v_a_498_ = lean_ctor_get(v___x_496_, 1);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_496_, 2);
v___x_499_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_474_, v___x_491_, v___x_493_, v_a_497_, v___y_475_, v_a_498_);
return v___x_499_;
}
else
{
lean_dec(v_docComment_x3f_474_);
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleDataDecl___boxed(lean_object* v_x_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lake_Formatters_fmtModuleDataDecl(v_x_518_, v_a_519_, v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1(){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_528_ = l_Lean_Fmt_fmtAttribute;
v___x_529_ = ((lean_object*)(l_Lake_Formatters_fmtModuleDataDecl___closed__1));
v___x_530_ = ((lean_object*)(l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___closed__1));
v___x_531_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtModuleDataDecl___boxed), 3, 0);
v___x_532_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_528_, v___x_529_, v___x_530_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1___boxed(lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1();
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLibraryDataDecl(lean_object* v_x_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_docComment_x3f_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lake_Formatters_fmtLibraryDataDecl___closed__1));
lean_inc(v_x_539_);
v___x_570_ = l_Lean_Syntax_isOfKind(v_x_539_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_x_539_);
v___x_571_ = l_Lean_Fmt_Error_partialFormatter;
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_a_541_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = l_Lean_Syntax_getArg(v_x_539_, v___x_573_);
v___x_575_ = l_Lean_Syntax_isNone(v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_574_);
v___x_577_ = l_Lean_Syntax_matchesNull(v___x_574_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_574_);
lean_dec(v_x_539_);
v___x_578_ = l_Lean_Fmt_Error_partialFormatter;
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_a_541_);
return v___x_579_;
}
else
{
lean_object* v_docComment_x3f_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_docComment_x3f_580_ = l_Lean_Syntax_getArg(v___x_574_, v___x_573_);
lean_dec(v___x_574_);
v___x_581_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__10));
lean_inc(v_docComment_x3f_580_);
v___x_582_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v_docComment_x3f_580_);
lean_dec(v_x_539_);
v___x_583_ = l_Lean_Fmt_Error_partialFormatter;
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_a_541_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_docComment_x3f_580_);
v_docComment_x3f_543_ = v___x_585_;
v___y_544_ = v_a_540_;
v___y_545_ = v_a_541_;
goto v___jp_542_;
}
}
}
else
{
lean_object* v___x_586_; 
lean_dec(v___x_574_);
v___x_586_ = lean_box(0);
v_docComment_x3f_543_ = v___x_586_;
v___y_544_ = v_a_540_;
v___y_545_ = v_a_541_;
goto v___jp_542_;
}
}
v___jp_542_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_546_ = lean_unsigned_to_nat(2u);
v___x_547_ = l_Lean_Syntax_getArg(v_x_539_, v___x_546_);
v___x_548_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__1));
lean_inc(v___x_547_);
v___x_549_ = l_Lean_Syntax_isOfKind(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v___x_547_);
lean_dec(v_docComment_x3f_543_);
lean_dec(v_x_539_);
v___x_550_ = l_Lean_Fmt_Error_partialFormatter;
v___x_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___y_545_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v_libraryDataTk_553_; lean_object* v___x_554_; lean_object* v_typeAscriptionTk_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_552_ = lean_unsigned_to_nat(1u);
v_libraryDataTk_553_ = l_Lean_Syntax_getArg(v_x_539_, v___x_552_);
v___x_554_ = lean_unsigned_to_nat(3u);
v_typeAscriptionTk_555_ = l_Lean_Syntax_getArg(v_x_539_, v___x_554_);
v___x_556_ = lean_unsigned_to_nat(4u);
v___x_557_ = l_Lean_Syntax_getArg(v_x_539_, v___x_556_);
lean_dec(v_x_539_);
v___x_558_ = lean_mk_empty_array_with_capacity(v___x_552_);
v___x_559_ = lean_array_push(v___x_558_, v_libraryDataTk_553_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_547_);
v___x_562_ = ((lean_object*)(l_Lake_Formatters_fmtDataTypeDecl___closed__2));
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v_typeAscriptionTk_555_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_557_);
v___x_565_ = l_Lean_Fmt_fmtDeclarationSignature(v___x_559_, v___x_560_, v___x_561_, v___x_562_, v___x_563_, v___x_564_, v___y_544_, v___y_545_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v___x_568_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
v_a_567_ = lean_ctor_get(v___x_565_, 1);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_565_, 2);
v___x_568_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_543_, v___x_560_, v___x_562_, v_a_566_, v___y_544_, v_a_567_);
return v___x_568_;
}
else
{
lean_dec(v_docComment_x3f_543_);
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLibraryDataDecl___boxed(lean_object* v_x_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lake_Formatters_fmtLibraryDataDecl(v_x_587_, v_a_588_, v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1(){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_597_ = l_Lean_Fmt_fmtAttribute;
v___x_598_ = ((lean_object*)(l_Lake_Formatters_fmtLibraryDataDecl___closed__1));
v___x_599_ = ((lean_object*)(l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___closed__1));
v___x_600_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtLibraryDataDecl___boxed), 3, 0);
v___x_601_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_597_, v___x_598_, v___x_599_, v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1___boxed(lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1();
return v_res_603_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Formatters_Build_Data(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtDataTypeDecl___regBuiltin_Lake_Formatters_fmtDataTypeDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtBuiltinFacetCommand___regBuiltin_Lake_Formatters_fmtBuiltinFacetCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtFacetDataDecl___regBuiltin_Lake_Formatters_fmtFacetDataDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtCustomDataDecl___regBuiltin_Lake_Formatters_fmtCustomDataDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtPackageDataDecl___regBuiltin_Lake_Formatters_fmtPackageDataDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtModuleDataDecl___regBuiltin_Lake_Formatters_fmtModuleDataDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Build_Data_0__Lake_Formatters_fmtLibraryDataDecl___regBuiltin_Lake_Formatters_fmtLibraryDataDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Build_Data(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Formatters_Build_Data(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lake_Build_Data(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Formatters_Build_Data(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Formatters_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Formatters_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Formatters_Build_Data(builtin);
}
#ifdef __cplusplus
}
#endif
