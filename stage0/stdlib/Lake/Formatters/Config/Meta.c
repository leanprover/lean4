// Lean compiler output
// Module: Lake.Formatters.Config.Meta
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lake.Config.Meta import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_binder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithDeclModifiers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtBinders(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtStructureLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__0_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "configField"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__1_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__2_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 254, 146, 249, 6, 137, 67, 241)}};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__2_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__4_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__6_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__7_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__7_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__7_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__7_value;
static const lean_array_object l_Lake_Formatters_fmtConfigField___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__8_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__9_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__10 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__10_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__11_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__11_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__11_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__10_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__11 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__11_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__12 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__12_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__13 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__13_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__14_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__14_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__14_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__13_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__14 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__14_value;
static const lean_string_object l_Lake_Formatters_fmtConfigField___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__15 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__15_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigField___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__15_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_Formatters_fmtConfigField___closed__16 = (const lean_object*)&l_Lake_Formatters_fmtConfigField___closed__16_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtConfigField(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtConfigField___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Formatters"};
static const lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__0_value;
static const lean_string_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtConfigField"};
static const lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__1_value;
static const lean_ctor_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 64, 189, 91, 65, 26, 96, 245)}};
static const lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__2 = (const lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtConfigDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configDecl"};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 67, 129, 86, 42, 160, 126, 252)}};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtConfigDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__3_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtConfigDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optDeriving"};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__5_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__5_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__5_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(215, 163, 253, 206, 79, 89, 101, 240)}};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtConfigDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__6_value;
static const lean_string_object l_Lake_Formatters_fmtConfigDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__7_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__8_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(243, 64, 60, 42, 244, 245, 53, 52)}};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__8_value;
static const lean_string_object l_Lake_Formatters_fmtConfigDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structCtor"};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__9_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__10_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__10_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__10_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__9_value),LEAN_SCALAR_PTR_LITERAL(56, 67, 52, 180, 140, 36, 149, 125)}};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__10 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__10_value;
static const lean_string_object l_Lake_Formatters_fmtConfigDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " where "};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__11 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__11_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__12_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__11_value),LEAN_SCALAR_PTR_LITERAL(197, 177, 143, 70, 3, 238, 86, 51)}};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__12 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__12_value;
static const lean_string_object l_Lake_Formatters_fmtConfigDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extends"};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__13 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__13_value;
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__14_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__14_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtConfigDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__14_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__13_value),LEAN_SCALAR_PTR_LITERAL(231, 24, 97, 144, 91, 250, 92, 29)}};
static const lean_object* l_Lake_Formatters_fmtConfigDecl___closed__14 = (const lean_object*)&l_Lake_Formatters_fmtConfigDecl___closed__14_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtConfigDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtConfigDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtConfigDecl"};
static const lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtConfigField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 230, 178, 188, 210, 166, 23, 195)}};
static const lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtConfigField(lean_object* v_x_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__2));
lean_inc(v_x_34_);
v___x_38_ = l_Lean_Syntax_isOfKind(v_x_34_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_x_34_);
v___x_39_ = l_Lean_Fmt_Error_partialFormatter;
v___x_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v_a_36_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v_declModifiers_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v_declModifiers_42_ = l_Lean_Syntax_getArg(v_x_34_, v___x_41_);
v___x_43_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__7));
lean_inc(v_declModifiers_42_);
v___x_44_ = l_Lean_Syntax_isOfKind(v_declModifiers_42_, v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v_declModifiers_42_);
lean_dec(v_x_34_);
v___x_45_ = l_Lean_Fmt_Error_partialFormatter;
v___x_46_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v_a_36_);
return v___x_46_;
}
else
{
lean_object* v___x_47_; lean_object* v___y_49_; lean_object* v___y_50_; lean_object* v___y_51_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___y_58_; lean_object* v___y_59_; lean_object* v___y_60_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v___y_142_; lean_object* v___y_143_; lean_object* v___y_144_; lean_object* v___y_145_; lean_object* v___y_146_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v_colonEqTk_x3f_149_; lean_object* v_defVal_x3f_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v_id_x3f_166_; lean_object* v_atTk_x3f_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_197_ = l_Lean_Syntax_getArg(v_x_34_, v___x_47_);
v___x_198_ = l_Lean_Syntax_isNone(v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_197_);
v___x_200_ = l_Lean_Syntax_matchesNull(v___x_197_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v___x_197_);
lean_dec(v_declModifiers_42_);
lean_dec(v_x_34_);
v___x_201_ = l_Lean_Fmt_Error_partialFormatter;
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_36_);
return v___x_202_;
}
else
{
lean_object* v_id_x3f_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_id_x3f_203_ = l_Lean_Syntax_getArg(v___x_197_, v___x_41_);
v___x_204_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__16));
lean_inc(v_id_x3f_203_);
v___x_205_ = l_Lean_Syntax_isOfKind(v_id_x3f_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_id_x3f_203_);
lean_dec(v___x_197_);
lean_dec(v_declModifiers_42_);
lean_dec(v_x_34_);
v___x_206_ = l_Lean_Fmt_Error_partialFormatter;
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_a_36_);
return v___x_207_;
}
else
{
lean_object* v_atTk_x3f_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_atTk_x3f_208_ = l_Lean_Syntax_getArg(v___x_197_, v___x_47_);
lean_dec(v___x_197_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v_id_x3f_203_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v_atTk_x3f_208_);
v_id_x3f_166_ = v___x_209_;
v_atTk_x3f_167_ = v___x_210_;
v___y_168_ = v_a_35_;
v___y_169_ = v_a_36_;
goto v___jp_165_;
}
}
}
else
{
lean_object* v___x_211_; 
lean_dec(v___x_197_);
v___x_211_ = lean_box(0);
v_id_x3f_166_ = v___x_211_;
v_atTk_x3f_167_ = v___x_211_;
v___y_168_ = v_a_35_;
v___y_169_ = v_a_36_;
goto v___jp_165_;
}
v___jp_48_:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Fmt_fmt_x3f(v___y_60_, v___y_57_, v___y_56_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_62_);
v_a_63_ = lean_ctor_get(v___x_61_, 1);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_61_, 2);
lean_inc_ref(v___y_55_);
v___x_64_ = l_Lean_Fmt_Layouts_sepFill(v___y_55_, v___y_58_);
lean_dec_ref(v___y_58_);
v___x_65_ = lean_mk_empty_array_with_capacity(v___y_53_);
v___x_66_ = lean_array_push(v___x_65_, v___y_50_);
v___x_67_ = lean_array_push(v___x_66_, v___y_54_);
v___x_68_ = lean_array_push(v___x_67_, v___x_64_);
v___x_69_ = 0;
v___x_70_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_70_, 0, v___x_44_);
lean_ctor_set_uint8(v___x_70_, 1, v___x_69_);
lean_ctor_set_uint8(v___x_70_, 2, v___x_44_);
lean_ctor_set_uint8(v___x_70_, 3, v___x_44_);
v___x_71_ = l_Lean_Fmt_Layouts_infixOperator(v___x_68_, v___x_70_);
lean_dec_ref_known(v___x_70_, 0);
v___x_72_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__8));
v___x_73_ = lean_mk_empty_array_with_capacity(v___x_47_);
v___x_74_ = lean_array_push(v___x_73_, v___x_71_);
v___x_75_ = lean_box(1);
v___x_76_ = l_Lean_Fmt_Layouts_binder(v___x_72_, v___x_74_, v___y_52_, v___y_59_, v___y_49_, v___y_51_, v_a_62_, v___x_72_, v___x_75_);
lean_dec_ref(v___y_52_);
lean_dec_ref(v___x_74_);
v___x_77_ = l_Lean_Fmt_fmtDeclWithDeclModifiers(v_declModifiers_42_, v___x_76_, v___y_57_, v_a_63_);
return v___x_77_;
}
else
{
lean_dec_ref(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec_ref(v___y_54_);
lean_dec_ref(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v_declModifiers_42_);
return v___x_61_;
}
}
v___jp_78_:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Fmt_fmt_x3f(v___y_90_, v___y_86_, v___y_79_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_94_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v___x_91_, 1);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_91_, 2);
v___x_94_ = l_Lean_Fmt_fmt_x3f(v___y_83_, v___y_86_, v_a_93_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_97_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
v_a_96_ = lean_ctor_get(v___x_94_, 1);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_94_, 2);
v___x_97_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_82_, v___y_86_, v_a_96_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v_a_99_; lean_object* v___x_100_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
v_a_99_ = lean_ctor_get(v___x_97_, 1);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_97_, 2);
v___x_100_ = l_Lean_Fmt_fmtBinders(v___y_89_, v___y_86_, v_a_99_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v___x_103_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
v_a_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_100_, 2);
v___x_103_ = l_Lean_Fmt_fmt(v___y_88_, v___y_86_, v_a_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v_a_105_; lean_object* v___x_106_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
v_a_105_ = lean_ctor_get(v___x_103_, 1);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_103_, 2);
v___x_106_ = l_Lean_Fmt_fmt(v___y_87_, v___y_86_, v_a_105_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v___x_109_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
v_a_108_ = lean_ctor_get(v___x_106_, 1);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_106_, 2);
v___x_109_ = l_Lean_Fmt_fmt_x3f(v___y_80_, v___y_86_, v_a_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
if (lean_obj_tag(v___y_84_) == 0)
{
lean_object* v_a_110_; lean_object* v_a_111_; lean_object* v___x_112_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
v_a_111_ = lean_ctor_get(v___x_109_, 1);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_109_, 2);
v___x_112_ = lean_box(0);
v___y_49_ = v_a_107_;
v___y_50_ = v_a_92_;
v___y_51_ = v_a_110_;
v___y_52_ = v_a_101_;
v___y_53_ = v___y_81_;
v___y_54_ = v_a_95_;
v___y_55_ = v___y_85_;
v___y_56_ = v_a_111_;
v___y_57_ = v___y_86_;
v___y_58_ = v_a_98_;
v___y_59_ = v_a_104_;
v___y_60_ = v___x_112_;
goto v___jp_48_;
}
else
{
lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v_val_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_a_113_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_113_);
v_a_114_ = lean_ctor_get(v___x_109_, 1);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_109_, 2);
v_val_115_ = lean_ctor_get(v___y_84_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___y_84_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___y_84_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_val_115_);
lean_dec(v___y_84_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_val_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
v___y_49_ = v_a_107_;
v___y_50_ = v_a_92_;
v___y_51_ = v_a_113_;
v___y_52_ = v_a_101_;
v___y_53_ = v___y_81_;
v___y_54_ = v_a_95_;
v___y_55_ = v___y_85_;
v___y_56_ = v_a_114_;
v___y_57_ = v___y_86_;
v___y_58_ = v_a_98_;
v___y_59_ = v_a_104_;
v___y_60_ = v___x_120_;
goto v___jp_48_;
}
}
}
}
else
{
lean_dec(v_a_107_);
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
lean_dec(v_a_92_);
lean_dec(v___y_84_);
lean_dec(v_declModifiers_42_);
return v___x_109_;
}
}
else
{
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
lean_dec(v_a_92_);
lean_dec(v___y_84_);
lean_dec(v___y_80_);
lean_dec(v_declModifiers_42_);
return v___x_106_;
}
}
else
{
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
lean_dec(v_a_92_);
lean_dec(v___y_87_);
lean_dec(v___y_84_);
lean_dec(v___y_80_);
lean_dec(v_declModifiers_42_);
return v___x_103_;
}
}
else
{
lean_object* v_a_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_a_98_);
lean_dec(v_a_95_);
lean_dec(v_a_92_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
lean_dec(v___y_84_);
lean_dec(v___y_80_);
lean_dec(v_declModifiers_42_);
v_a_123_ = lean_ctor_get(v___x_100_, 0);
v_a_124_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_100_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_inc(v_a_123_);
lean_dec(v___x_100_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_123_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_dec(v_a_95_);
lean_dec(v_a_92_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
lean_dec(v___y_84_);
lean_dec(v___y_80_);
lean_dec(v_declModifiers_42_);
v_a_132_ = lean_ctor_get(v___x_97_, 0);
v_a_133_ = lean_ctor_get(v___x_97_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_97_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_inc(v_a_132_);
lean_dec(v___x_97_);
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
lean_dec(v_a_92_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_80_);
lean_dec(v_declModifiers_42_);
return v___x_94_;
}
}
else
{
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
lean_dec(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_80_);
lean_dec(v_declModifiers_42_);
return v___x_91_;
}
}
v___jp_141_:
{
lean_object* v_binders_153_; lean_object* v___x_154_; lean_object* v_ids_155_; 
v_binders_153_ = l_Lean_Syntax_getArgs(v___y_144_);
lean_dec(v___y_144_);
v___x_154_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__9));
v_ids_155_ = l_Lean_Syntax_getArgs(v___y_145_);
lean_dec(v___y_145_);
if (lean_obj_tag(v___y_146_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
v___y_79_ = v___y_152_;
v___y_80_ = v_colonEqTk_x3f_149_;
v___y_81_ = v___y_143_;
v___y_82_ = v_ids_155_;
v___y_83_ = v___y_142_;
v___y_84_ = v_defVal_x3f_150_;
v___y_85_ = v___x_154_;
v___y_86_ = v___y_151_;
v___y_87_ = v___y_147_;
v___y_88_ = v___y_148_;
v___y_89_ = v_binders_153_;
v___y_90_ = v___x_156_;
goto v___jp_78_;
}
else
{
lean_object* v_val_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_val_157_ = lean_ctor_get(v___y_146_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___y_146_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___y_146_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_val_157_);
lean_dec(v___y_146_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_val_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
v___y_79_ = v___y_152_;
v___y_80_ = v_colonEqTk_x3f_149_;
v___y_81_ = v___y_143_;
v___y_82_ = v_ids_155_;
v___y_83_ = v___y_142_;
v___y_84_ = v_defVal_x3f_150_;
v___y_85_ = v___x_154_;
v___y_86_ = v___y_151_;
v___y_87_ = v___y_147_;
v___y_88_ = v___y_148_;
v___y_89_ = v_binders_153_;
v___y_90_ = v___x_162_;
goto v___jp_78_;
}
}
}
}
v___jp_165_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_170_ = lean_unsigned_to_nat(3u);
v___x_171_ = l_Lean_Syntax_getArg(v_x_34_, v___x_170_);
v___x_172_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__11));
lean_inc(v___x_171_);
v___x_173_ = l_Lean_Syntax_isOfKind(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v___x_171_);
lean_dec(v_atTk_x3f_167_);
lean_dec(v_id_x3f_166_);
lean_dec(v_declModifiers_42_);
lean_dec(v_x_34_);
v___x_174_ = l_Lean_Fmt_Error_partialFormatter;
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___y_169_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = l_Lean_Syntax_getArg(v___x_171_, v___x_47_);
v___x_177_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__14));
lean_inc(v___x_176_);
v___x_178_ = l_Lean_Syntax_isOfKind(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v___x_176_);
lean_dec(v___x_171_);
lean_dec(v_atTk_x3f_167_);
lean_dec(v_id_x3f_166_);
lean_dec(v_declModifiers_42_);
lean_dec(v_x_34_);
v___x_179_ = l_Lean_Fmt_Error_partialFormatter;
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___y_169_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_typeAscriptionTk_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_181_ = lean_unsigned_to_nat(2u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_34_, v___x_181_);
v___x_183_ = l_Lean_Syntax_getArg(v___x_171_, v___x_41_);
lean_dec(v___x_171_);
v_typeAscriptionTk_184_ = l_Lean_Syntax_getArg(v___x_176_, v___x_41_);
v___x_185_ = l_Lean_Syntax_getArg(v___x_176_, v___x_47_);
lean_dec(v___x_176_);
v___x_186_ = lean_unsigned_to_nat(4u);
v___x_187_ = l_Lean_Syntax_getArg(v_x_34_, v___x_186_);
lean_dec(v_x_34_);
v___x_188_ = l_Lean_Syntax_isNone(v___x_187_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; 
lean_inc(v___x_187_);
v___x_189_ = l_Lean_Syntax_matchesNull(v___x_187_, v___x_181_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v___x_187_);
lean_dec(v___x_185_);
lean_dec(v_typeAscriptionTk_184_);
lean_dec(v___x_183_);
lean_dec(v___x_182_);
lean_dec(v_atTk_x3f_167_);
lean_dec(v_id_x3f_166_);
lean_dec(v_declModifiers_42_);
v___x_190_ = l_Lean_Fmt_Error_partialFormatter;
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___y_169_);
return v___x_191_;
}
else
{
lean_object* v_colonEqTk_x3f_192_; lean_object* v_defVal_x3f_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_colonEqTk_x3f_192_ = l_Lean_Syntax_getArg(v___x_187_, v___x_41_);
v_defVal_x3f_193_ = l_Lean_Syntax_getArg(v___x_187_, v___x_47_);
lean_dec(v___x_187_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_colonEqTk_x3f_192_);
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v_defVal_x3f_193_);
v___y_142_ = v_atTk_x3f_167_;
v___y_143_ = v___x_170_;
v___y_144_ = v___x_183_;
v___y_145_ = v___x_182_;
v___y_146_ = v_id_x3f_166_;
v___y_147_ = v___x_185_;
v___y_148_ = v_typeAscriptionTk_184_;
v_colonEqTk_x3f_149_ = v___x_194_;
v_defVal_x3f_150_ = v___x_195_;
v___y_151_ = v___y_168_;
v___y_152_ = v___y_169_;
goto v___jp_141_;
}
}
else
{
lean_object* v___x_196_; 
lean_dec(v___x_187_);
v___x_196_ = lean_box(0);
v___y_142_ = v_atTk_x3f_167_;
v___y_143_ = v___x_170_;
v___y_144_ = v___x_183_;
v___y_145_ = v___x_182_;
v___y_146_ = v_id_x3f_166_;
v___y_147_ = v___x_185_;
v___y_148_ = v_typeAscriptionTk_184_;
v_colonEqTk_x3f_149_ = v___x_196_;
v_defVal_x3f_150_ = v___x_196_;
v___y_151_ = v___y_168_;
v___y_152_ = v___y_169_;
goto v___jp_141_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtConfigField___boxed(lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lake_Formatters_fmtConfigField(v_x_212_, v_a_213_, v_a_214_);
lean_dec_ref(v_a_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1(){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_223_ = l_Lean_Fmt_fmtAttribute;
v___x_224_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__2));
v___x_225_ = ((lean_object*)(l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___closed__2));
v___x_226_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtConfigField___boxed), 3, 0);
v___x_227_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_223_, v___x_224_, v___x_225_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1___boxed(lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1();
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__1(size_t v_sz_230_, size_t v_i_231_, lean_object* v_bs_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = lean_usize_dec_lt(v_i_231_, v_sz_230_);
if (v___x_233_ == 0)
{
return v_bs_232_;
}
else
{
lean_object* v_v_234_; lean_object* v___x_235_; lean_object* v_bs_x27_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; 
v_v_234_ = lean_array_uget(v_bs_232_, v_i_231_);
v___x_235_ = lean_unsigned_to_nat(0u);
v_bs_x27_236_ = lean_array_uset(v_bs_232_, v_i_231_, v___x_235_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_231_, v___x_237_);
v___x_239_ = lean_array_uset(v_bs_x27_236_, v_i_231_, v_v_234_);
v_i_231_ = v___x_238_;
v_bs_232_ = v___x_239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__1___boxed(lean_object* v_sz_241_, lean_object* v_i_242_, lean_object* v_bs_243_){
_start:
{
size_t v_sz_boxed_244_; size_t v_i_boxed_245_; lean_object* v_res_246_; 
v_sz_boxed_244_ = lean_unbox_usize(v_sz_241_);
lean_dec(v_sz_241_);
v_i_boxed_245_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__1(v_sz_boxed_244_, v_i_boxed_245_, v_bs_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__0(size_t v_sz_247_, size_t v_i_248_, lean_object* v_bs_249_){
_start:
{
uint8_t v___x_250_; 
v___x_250_ = lean_usize_dec_lt(v_i_248_, v_sz_247_);
if (v___x_250_ == 0)
{
return v_bs_249_;
}
else
{
lean_object* v_v_251_; lean_object* v___x_252_; lean_object* v_bs_x27_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; 
v_v_251_ = lean_array_uget(v_bs_249_, v_i_248_);
v___x_252_ = lean_unsigned_to_nat(0u);
v_bs_x27_253_ = lean_array_uset(v_bs_249_, v_i_248_, v___x_252_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_248_, v___x_254_);
v___x_256_ = lean_array_uset(v_bs_x27_253_, v_i_248_, v_v_251_);
v_i_248_ = v___x_255_;
v_bs_249_ = v___x_256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__0___boxed(lean_object* v_sz_258_, lean_object* v_i_259_, lean_object* v_bs_260_){
_start:
{
size_t v_sz_boxed_261_; size_t v_i_boxed_262_; lean_object* v_res_263_; 
v_sz_boxed_261_ = lean_unbox_usize(v_sz_258_);
lean_dec(v_sz_258_);
v_i_boxed_262_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__0(v_sz_boxed_261_, v_i_boxed_262_, v_bs_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtConfigDecl(lean_object* v_x_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___y_305_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__1));
lean_inc(v_x_301_);
v___x_309_ = l_Lean_Syntax_isOfKind(v_x_301_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_x_301_);
v___x_310_ = l_Lean_Fmt_Error_partialFormatter;
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_303_);
return v___x_311_;
}
else
{
lean_object* v___x_312_; lean_object* v_declModifiers_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v_declModifiers_313_ = l_Lean_Syntax_getArg(v_x_301_, v___x_312_);
v___x_314_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__7));
lean_inc(v_declModifiers_313_);
v___x_315_ = l_Lean_Syntax_isOfKind(v_declModifiers_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___x_316_ = l_Lean_Fmt_Error_partialFormatter;
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_a_303_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v_declId_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(2u);
v_declId_319_ = l_Lean_Syntax_getArg(v_x_301_, v___x_318_);
v___x_320_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__3));
lean_inc(v_declId_319_);
v___x_321_ = l_Lean_Syntax_isOfKind(v_declId_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___x_322_ = l_Lean_Fmt_Error_partialFormatter;
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_a_303_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v_configurationTk_325_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v_sepTk_x3f_402_; lean_object* v_structCtor_x3f_403_; lean_object* v_configFields_x3f_404_; lean_object* v_optDeriving_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v_sepTk_x3f_421_; lean_object* v_structCtor_x3f_422_; lean_object* v_configFields_x3f_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v_structCtor_x3f_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v_sepTk_x3f_448_; lean_object* v_structCtor_x3f_449_; lean_object* v_configFields_x3f_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v_structCtor_x3f_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v_structCtor_x3f_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v_extends_x3f_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v_typeAscriptionTk_x3f_547_; lean_object* v_type_x3f_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v_configurationTk_325_ = l_Lean_Syntax_getArg(v_x_301_, v___x_324_);
v___x_396_ = lean_unsigned_to_nat(3u);
v___x_397_ = l_Lean_Syntax_getArg(v_x_301_, v___x_396_);
v___x_564_ = lean_unsigned_to_nat(4u);
v___x_565_ = l_Lean_Syntax_getArg(v_x_301_, v___x_564_);
v___x_566_ = l_Lean_Syntax_isNone(v___x_565_);
if (v___x_566_ == 0)
{
uint8_t v___x_567_; 
lean_inc(v___x_565_);
v___x_567_ = l_Lean_Syntax_matchesNull(v___x_565_, v___x_324_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v___x_565_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___x_568_ = l_Lean_Fmt_Error_partialFormatter;
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v_a_303_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = l_Lean_Syntax_getArg(v___x_565_, v___x_312_);
lean_dec(v___x_565_);
v___x_571_ = ((lean_object*)(l_Lake_Formatters_fmtConfigField___closed__14));
lean_inc(v___x_570_);
v___x_572_ = l_Lean_Syntax_isOfKind(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_570_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___x_573_ = l_Lean_Fmt_Error_partialFormatter;
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v_a_303_);
return v___x_574_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_575_; lean_object* v_type_x3f_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_typeAscriptionTk_x3f_575_ = l_Lean_Syntax_getArg(v___x_570_, v___x_312_);
v_type_x3f_576_ = l_Lean_Syntax_getArg(v___x_570_, v___x_324_);
lean_dec(v___x_570_);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_typeAscriptionTk_x3f_575_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_type_x3f_576_);
v_typeAscriptionTk_x3f_547_ = v___x_577_;
v_type_x3f_548_ = v___x_578_;
v___y_549_ = v_a_302_;
v___y_550_ = v_a_303_;
goto v___jp_546_;
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v___x_565_);
v___x_579_ = lean_box(0);
v_typeAscriptionTk_x3f_547_ = v___x_579_;
v_type_x3f_548_ = v___x_579_;
v___y_549_ = v_a_302_;
v___y_550_ = v_a_303_;
goto v___jp_546_;
}
v___jp_326_:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Fmt_fmtStructureLike(v_configurationTk_325_, v_declId_319_, v___y_328_, v___y_327_, v___y_333_, v___y_335_, v___y_330_, v___y_329_, v___y_336_, v___y_332_, v___y_334_, v___y_331_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v_a_339_; lean_object* v___x_340_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
v_a_339_ = lean_ctor_get(v___x_337_, 1);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_337_, 2);
v___x_340_ = l_Lean_Fmt_fmtDeclWithDeclModifiers(v_declModifiers_313_, v_a_338_, v___y_334_, v_a_339_);
return v___x_340_;
}
else
{
lean_dec(v_declModifiers_313_);
return v___x_337_;
}
}
v___jp_341_:
{
if (lean_obj_tag(v___y_342_) == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
v___y_327_ = v___y_344_;
v___y_328_ = v___y_343_;
v___y_329_ = v___y_351_;
v___y_330_ = v___y_345_;
v___y_331_ = v___y_346_;
v___y_332_ = v___y_348_;
v___y_333_ = v___y_347_;
v___y_334_ = v___y_349_;
v___y_335_ = v___y_350_;
v___y_336_ = v___x_352_;
goto v___jp_326_;
}
else
{
lean_object* v_val_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_val_353_ = lean_ctor_get(v___y_342_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___y_342_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___y_342_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_val_353_);
lean_dec(v___y_342_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_val_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
v___y_327_ = v___y_344_;
v___y_328_ = v___y_343_;
v___y_329_ = v___y_351_;
v___y_330_ = v___y_345_;
v___y_331_ = v___y_346_;
v___y_332_ = v___y_348_;
v___y_333_ = v___y_347_;
v___y_334_ = v___y_349_;
v___y_335_ = v___y_350_;
v___y_336_ = v___x_358_;
goto v___jp_326_;
}
}
}
}
v___jp_361_:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Fmt_fmtStructureLike(v_configurationTk_325_, v_declId_319_, v___y_368_, v___y_362_, v___y_367_, v___y_369_, v___y_370_, v___y_364_, v___y_371_, v___y_366_, v___y_365_, v___y_363_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v_a_374_; lean_object* v___x_375_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
v_a_374_ = lean_ctor_get(v___x_372_, 1);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_372_, 2);
v___x_375_ = l_Lean_Fmt_fmtDeclWithDeclModifiers(v_declModifiers_313_, v_a_373_, v___y_365_, v_a_374_);
return v___x_375_;
}
else
{
lean_dec(v_declModifiers_313_);
return v___x_372_;
}
}
v___jp_376_:
{
if (lean_obj_tag(v___y_377_) == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_box(0);
v___y_362_ = v___y_378_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_386_;
v___y_365_ = v___y_380_;
v___y_366_ = v___y_381_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_382_;
v___y_369_ = v___y_384_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_387_;
goto v___jp_361_;
}
else
{
lean_object* v_val_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_val_388_ = lean_ctor_get(v___y_377_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___y_377_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___y_377_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_val_388_);
lean_dec(v___y_377_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_val_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
v___y_362_ = v___y_378_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_386_;
v___y_365_ = v___y_380_;
v___y_366_ = v___y_381_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_382_;
v___y_369_ = v___y_384_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_393_;
goto v___jp_361_;
}
}
}
}
v___jp_398_:
{
lean_object* v_binders_408_; size_t v_sz_409_; size_t v___x_410_; lean_object* v___x_411_; size_t v_sz_412_; lean_object* v___x_413_; 
v_binders_408_ = l_Lean_Syntax_getArgs(v___x_397_);
lean_dec(v___x_397_);
v_sz_409_ = lean_array_size(v_binders_408_);
v___x_410_ = ((size_t)0ULL);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__0(v_sz_409_, v___x_410_, v_binders_408_);
v_sz_412_ = lean_array_size(v___x_411_);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__1(v_sz_412_, v___x_410_, v___x_411_);
if (lean_obj_tag(v_structCtor_x3f_403_) == 0)
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
v___y_342_ = v_configFields_x3f_404_;
v___y_343_ = v___x_413_;
v___y_344_ = v___y_399_;
v___y_345_ = v_sepTk_x3f_402_;
v___y_346_ = v___y_407_;
v___y_347_ = v___y_400_;
v___y_348_ = v_optDeriving_405_;
v___y_349_ = v___y_406_;
v___y_350_ = v___y_401_;
v___y_351_ = v___x_414_;
goto v___jp_341_;
}
else
{
lean_object* v_val_415_; 
v_val_415_ = lean_ctor_get(v_structCtor_x3f_403_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v_structCtor_x3f_403_, 1);
v___y_342_ = v_configFields_x3f_404_;
v___y_343_ = v___x_413_;
v___y_344_ = v___y_399_;
v___y_345_ = v_sepTk_x3f_402_;
v___y_346_ = v___y_407_;
v___y_347_ = v___y_400_;
v___y_348_ = v_optDeriving_405_;
v___y_349_ = v___y_406_;
v___y_350_ = v___y_401_;
v___y_351_ = v_val_415_;
goto v___jp_341_;
}
}
v___jp_416_:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__5));
lean_inc(v___y_418_);
v___x_427_ = l_Lean_Syntax_isOfKind(v___y_418_, v___x_426_);
if (v___x_427_ == 0)
{
lean_dec(v_configFields_x3f_423_);
lean_dec(v_structCtor_x3f_422_);
lean_dec(v_sepTk_x3f_421_);
lean_dec(v___y_420_);
lean_dec(v___y_419_);
lean_dec(v___y_418_);
lean_dec(v___y_417_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
v___y_305_ = v___y_425_;
goto v___jp_304_;
}
else
{
v___y_399_ = v___y_417_;
v___y_400_ = v___y_419_;
v___y_401_ = v___y_420_;
v_sepTk_x3f_402_ = v_sepTk_x3f_421_;
v_structCtor_x3f_403_ = v_structCtor_x3f_422_;
v_configFields_x3f_404_ = v_configFields_x3f_423_;
v_optDeriving_405_ = v___y_418_;
v___y_406_ = v___y_424_;
v___y_407_ = v___y_425_;
goto v___jp_398_;
}
}
v___jp_428_:
{
lean_object* v___x_438_; lean_object* v_configFields_x3f_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_438_ = l_Lean_Syntax_getArg(v___y_429_, v___x_318_);
lean_dec(v___y_429_);
v_configFields_x3f_439_ = l_Lean_Syntax_getArgs(v___x_438_);
lean_dec(v___x_438_);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v___y_433_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_structCtor_x3f_435_);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_configFields_x3f_439_);
v___y_417_ = v___y_430_;
v___y_418_ = v___y_431_;
v___y_419_ = v___y_432_;
v___y_420_ = v___y_434_;
v_sepTk_x3f_421_ = v___x_440_;
v_structCtor_x3f_422_ = v___x_441_;
v_configFields_x3f_423_ = v___x_442_;
v___y_424_ = v___y_436_;
v___y_425_ = v___y_437_;
goto v___jp_416_;
}
v___jp_443_:
{
lean_object* v___x_453_; lean_object* v_optDeriving_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_453_ = lean_unsigned_to_nat(7u);
v_optDeriving_454_ = l_Lean_Syntax_getArg(v_x_301_, v___x_453_);
lean_dec(v_x_301_);
v___x_455_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__5));
lean_inc(v_optDeriving_454_);
v___x_456_ = l_Lean_Syntax_isOfKind(v_optDeriving_454_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
lean_dec(v_configFields_x3f_450_);
lean_dec(v_structCtor_x3f_449_);
lean_dec(v_sepTk_x3f_448_);
v___x_457_ = l_Lean_Syntax_isNone(v___y_444_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
lean_inc(v___y_444_);
v___x_458_ = l_Lean_Syntax_matchesNull(v___y_444_, v___x_396_);
if (v___x_458_ == 0)
{
lean_dec(v_optDeriving_454_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
v___y_305_ = v___y_452_;
goto v___jp_304_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = l_Lean_Syntax_getArg(v___y_444_, v___x_312_);
v___x_460_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__8));
lean_inc(v___x_459_);
v___x_461_ = l_Lean_Syntax_isOfKind(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec(v___x_459_);
lean_dec(v_optDeriving_454_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
v___y_305_ = v___y_452_;
goto v___jp_304_;
}
else
{
lean_object* v_sepTk_x3f_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_sepTk_x3f_462_ = l_Lean_Syntax_getArg(v___x_459_, v___x_312_);
lean_dec(v___x_459_);
v___x_463_ = l_Lean_Syntax_getArg(v___y_444_, v___x_324_);
v___x_464_ = l_Lean_Syntax_isNone(v___x_463_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
lean_inc(v___x_463_);
v___x_465_ = l_Lean_Syntax_matchesNull(v___x_463_, v___x_324_);
if (v___x_465_ == 0)
{
lean_dec(v___x_463_);
lean_dec(v_sepTk_x3f_462_);
lean_dec(v_optDeriving_454_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
v___y_305_ = v___y_452_;
goto v___jp_304_;
}
else
{
lean_object* v_structCtor_x3f_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_structCtor_x3f_466_ = l_Lean_Syntax_getArg(v___x_463_, v___x_312_);
lean_dec(v___x_463_);
v___x_467_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__10));
lean_inc(v_structCtor_x3f_466_);
v___x_468_ = l_Lean_Syntax_isOfKind(v_structCtor_x3f_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_dec(v_structCtor_x3f_466_);
lean_dec(v_sepTk_x3f_462_);
lean_dec(v_optDeriving_454_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
v___y_305_ = v___y_452_;
goto v___jp_304_;
}
else
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v_structCtor_x3f_466_);
v___y_429_ = v___y_444_;
v___y_430_ = v___y_445_;
v___y_431_ = v_optDeriving_454_;
v___y_432_ = v___y_446_;
v___y_433_ = v_sepTk_x3f_462_;
v___y_434_ = v___y_447_;
v_structCtor_x3f_435_ = v___x_469_;
v___y_436_ = v___y_451_;
v___y_437_ = v___y_452_;
goto v___jp_428_;
}
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v___x_463_);
v___x_470_ = lean_box(0);
v___y_429_ = v___y_444_;
v___y_430_ = v___y_445_;
v___y_431_ = v_optDeriving_454_;
v___y_432_ = v___y_446_;
v___y_433_ = v_sepTk_x3f_462_;
v___y_434_ = v___y_447_;
v_structCtor_x3f_435_ = v___x_470_;
v___y_436_ = v___y_451_;
v___y_437_ = v___y_452_;
goto v___jp_428_;
}
}
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v___y_444_);
v___x_471_ = lean_box(0);
v___y_417_ = v___y_445_;
v___y_418_ = v_optDeriving_454_;
v___y_419_ = v___y_446_;
v___y_420_ = v___y_447_;
v_sepTk_x3f_421_ = v___x_471_;
v_structCtor_x3f_422_ = v___x_471_;
v_configFields_x3f_423_ = v___x_471_;
v___y_424_ = v___y_451_;
v___y_425_ = v___y_452_;
goto v___jp_416_;
}
}
else
{
lean_object* v_binders_472_; size_t v_sz_473_; size_t v___x_474_; lean_object* v___x_475_; size_t v_sz_476_; lean_object* v___x_477_; 
lean_dec(v___y_444_);
v_binders_472_ = l_Lean_Syntax_getArgs(v___x_397_);
lean_dec(v___x_397_);
v_sz_473_ = lean_array_size(v_binders_472_);
v___x_474_ = ((size_t)0ULL);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__0(v_sz_473_, v___x_474_, v_binders_472_);
v_sz_476_ = lean_array_size(v___x_475_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtConfigDecl_spec__1(v_sz_476_, v___x_474_, v___x_475_);
if (lean_obj_tag(v_structCtor_x3f_449_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
v___y_377_ = v_configFields_x3f_450_;
v___y_378_ = v___y_445_;
v___y_379_ = v___y_452_;
v___y_380_ = v___y_451_;
v___y_381_ = v_optDeriving_454_;
v___y_382_ = v___x_477_;
v___y_383_ = v___y_446_;
v___y_384_ = v___y_447_;
v___y_385_ = v_sepTk_x3f_448_;
v___y_386_ = v___x_478_;
goto v___jp_376_;
}
else
{
lean_object* v_val_479_; 
v_val_479_ = lean_ctor_get(v_structCtor_x3f_449_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v_structCtor_x3f_449_, 1);
v___y_377_ = v_configFields_x3f_450_;
v___y_378_ = v___y_445_;
v___y_379_ = v___y_452_;
v___y_380_ = v___y_451_;
v___y_381_ = v_optDeriving_454_;
v___y_382_ = v___x_477_;
v___y_383_ = v___y_446_;
v___y_384_ = v___y_447_;
v___y_385_ = v_sepTk_x3f_448_;
v___y_386_ = v_val_479_;
goto v___jp_376_;
}
}
}
v___jp_480_:
{
lean_object* v___x_489_; lean_object* v_configFields_x3f_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_489_ = l_Lean_Syntax_getArg(v___y_481_, v___x_318_);
v_configFields_x3f_490_ = l_Lean_Syntax_getArgs(v___x_489_);
lean_dec(v___x_489_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v___y_484_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_structCtor_x3f_486_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_configFields_x3f_490_);
v___y_444_ = v___y_481_;
v___y_445_ = v___y_482_;
v___y_446_ = v___y_483_;
v___y_447_ = v___y_485_;
v_sepTk_x3f_448_ = v___x_491_;
v_structCtor_x3f_449_ = v___x_492_;
v_configFields_x3f_450_ = v___x_493_;
v___y_451_ = v___y_487_;
v___y_452_ = v___y_488_;
goto v___jp_443_;
}
v___jp_494_:
{
lean_object* v___x_503_; lean_object* v_optDeriving_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_503_ = lean_unsigned_to_nat(7u);
v_optDeriving_504_ = l_Lean_Syntax_getArg(v_x_301_, v___x_503_);
lean_dec(v_x_301_);
v___x_505_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__5));
lean_inc(v_optDeriving_504_);
v___x_506_ = l_Lean_Syntax_isOfKind(v_optDeriving_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_dec(v_optDeriving_504_);
lean_dec(v_structCtor_x3f_500_);
lean_dec(v___y_499_);
lean_dec(v___y_498_);
lean_dec(v___y_497_);
lean_dec(v___y_496_);
lean_dec(v___y_495_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
v___y_305_ = v___y_502_;
goto v___jp_304_;
}
else
{
lean_object* v_configFields_x3f_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_configFields_x3f_507_ = l_Lean_Syntax_getArgs(v___y_498_);
lean_dec(v___y_498_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___y_496_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v_structCtor_x3f_500_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v_configFields_x3f_507_);
v___y_399_ = v___y_495_;
v___y_400_ = v___y_497_;
v___y_401_ = v___y_499_;
v_sepTk_x3f_402_ = v___x_508_;
v_structCtor_x3f_403_ = v___x_509_;
v_configFields_x3f_404_ = v___x_510_;
v_optDeriving_405_ = v_optDeriving_504_;
v___y_406_ = v___y_501_;
v___y_407_ = v___y_502_;
goto v___jp_398_;
}
}
v___jp_511_:
{
lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_unsigned_to_nat(6u);
v___x_518_ = l_Lean_Syntax_getArg(v_x_301_, v___x_517_);
v___x_519_ = l_Lean_Syntax_isNone(v___x_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; 
lean_inc(v___x_518_);
v___x_520_ = l_Lean_Syntax_matchesNull(v___x_518_, v___x_396_);
if (v___x_520_ == 0)
{
lean_dec(v___x_518_);
lean_dec(v_extends_x3f_514_);
lean_dec(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___y_305_ = v___y_516_;
goto v___jp_304_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = l_Lean_Syntax_getArg(v___x_518_, v___x_312_);
v___x_522_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__12));
lean_inc(v___x_521_);
v___x_523_ = l_Lean_Syntax_isOfKind(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__8));
lean_inc(v___x_521_);
v___x_525_ = l_Lean_Syntax_isOfKind(v___x_521_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v___x_521_);
lean_dec(v___x_518_);
lean_dec(v_extends_x3f_514_);
lean_dec(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___y_305_ = v___y_516_;
goto v___jp_304_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_sepTk_x3f_528_; uint8_t v___x_529_; 
v___x_526_ = l_Lean_Syntax_getArg(v___x_518_, v___x_324_);
v___x_527_ = l_Lean_Syntax_getArg(v___x_518_, v___x_318_);
lean_dec(v___x_518_);
v_sepTk_x3f_528_ = l_Lean_Syntax_getArg(v___x_521_, v___x_312_);
lean_dec(v___x_521_);
v___x_529_ = l_Lean_Syntax_isNone(v___x_526_);
if (v___x_529_ == 0)
{
uint8_t v___x_530_; 
lean_inc(v___x_526_);
v___x_530_ = l_Lean_Syntax_matchesNull(v___x_526_, v___x_324_);
if (v___x_530_ == 0)
{
lean_dec(v_sepTk_x3f_528_);
lean_dec(v___x_527_);
lean_dec(v___x_526_);
lean_dec(v_extends_x3f_514_);
lean_dec(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___y_305_ = v___y_516_;
goto v___jp_304_;
}
else
{
lean_object* v_structCtor_x3f_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_structCtor_x3f_531_ = l_Lean_Syntax_getArg(v___x_526_, v___x_312_);
lean_dec(v___x_526_);
v___x_532_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__10));
lean_inc(v_structCtor_x3f_531_);
v___x_533_ = l_Lean_Syntax_isOfKind(v_structCtor_x3f_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v_structCtor_x3f_531_);
lean_dec(v_sepTk_x3f_528_);
lean_dec(v___x_527_);
lean_dec(v_extends_x3f_514_);
lean_dec(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___y_305_ = v___y_516_;
goto v___jp_304_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_structCtor_x3f_531_);
v___y_495_ = v___y_512_;
v___y_496_ = v_sepTk_x3f_528_;
v___y_497_ = v___y_513_;
v___y_498_ = v___x_527_;
v___y_499_ = v_extends_x3f_514_;
v_structCtor_x3f_500_ = v___x_534_;
v___y_501_ = v___y_515_;
v___y_502_ = v___y_516_;
goto v___jp_494_;
}
}
}
else
{
lean_object* v___x_535_; 
lean_dec(v___x_526_);
v___x_535_ = lean_box(0);
v___y_495_ = v___y_512_;
v___y_496_ = v_sepTk_x3f_528_;
v___y_497_ = v___y_513_;
v___y_498_ = v___x_527_;
v___y_499_ = v_extends_x3f_514_;
v_structCtor_x3f_500_ = v___x_535_;
v___y_501_ = v___y_515_;
v___y_502_ = v___y_516_;
goto v___jp_494_;
}
}
}
else
{
lean_object* v_sepTk_x3f_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_sepTk_x3f_536_ = l_Lean_Syntax_getArg(v___x_521_, v___x_312_);
lean_dec(v___x_521_);
v___x_537_ = l_Lean_Syntax_getArg(v___x_518_, v___x_324_);
v___x_538_ = l_Lean_Syntax_isNone(v___x_537_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; 
lean_inc(v___x_537_);
v___x_539_ = l_Lean_Syntax_matchesNull(v___x_537_, v___x_324_);
if (v___x_539_ == 0)
{
lean_dec(v___x_537_);
lean_dec(v_sepTk_x3f_536_);
lean_dec(v___x_518_);
lean_dec(v_extends_x3f_514_);
lean_dec(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___y_305_ = v___y_516_;
goto v___jp_304_;
}
else
{
lean_object* v_structCtor_x3f_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_structCtor_x3f_540_ = l_Lean_Syntax_getArg(v___x_537_, v___x_312_);
lean_dec(v___x_537_);
v___x_541_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__10));
lean_inc(v_structCtor_x3f_540_);
v___x_542_ = l_Lean_Syntax_isOfKind(v_structCtor_x3f_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_dec(v_structCtor_x3f_540_);
lean_dec(v_sepTk_x3f_536_);
lean_dec(v___x_518_);
lean_dec(v_extends_x3f_514_);
lean_dec(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___y_305_ = v___y_516_;
goto v___jp_304_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_structCtor_x3f_540_);
v___y_481_ = v___x_518_;
v___y_482_ = v___y_512_;
v___y_483_ = v___y_513_;
v___y_484_ = v_sepTk_x3f_536_;
v___y_485_ = v_extends_x3f_514_;
v_structCtor_x3f_486_ = v___x_543_;
v___y_487_ = v___y_515_;
v___y_488_ = v___y_516_;
goto v___jp_480_;
}
}
}
else
{
lean_object* v___x_544_; 
lean_dec(v___x_537_);
v___x_544_ = lean_box(0);
v___y_481_ = v___x_518_;
v___y_482_ = v___y_512_;
v___y_483_ = v___y_513_;
v___y_484_ = v_sepTk_x3f_536_;
v___y_485_ = v_extends_x3f_514_;
v_structCtor_x3f_486_ = v___x_544_;
v___y_487_ = v___y_515_;
v___y_488_ = v___y_516_;
goto v___jp_480_;
}
}
}
}
else
{
lean_object* v___x_545_; 
v___x_545_ = lean_box(0);
v___y_444_ = v___x_518_;
v___y_445_ = v___y_512_;
v___y_446_ = v___y_513_;
v___y_447_ = v_extends_x3f_514_;
v_sepTk_x3f_448_ = v___x_545_;
v_structCtor_x3f_449_ = v___x_545_;
v_configFields_x3f_450_ = v___x_545_;
v___y_451_ = v___y_515_;
v___y_452_ = v___y_516_;
goto v___jp_443_;
}
}
v___jp_546_:
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_unsigned_to_nat(5u);
v___x_552_ = l_Lean_Syntax_getArg(v_x_301_, v___x_551_);
v___x_553_ = l_Lean_Syntax_isNone(v___x_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
lean_inc(v___x_552_);
v___x_554_ = l_Lean_Syntax_matchesNull(v___x_552_, v___x_324_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v___x_552_);
lean_dec(v_type_x3f_548_);
lean_dec(v_typeAscriptionTk_x3f_547_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___x_555_ = l_Lean_Fmt_Error_partialFormatter;
v___x_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___y_550_);
return v___x_556_;
}
else
{
lean_object* v_extends_x3f_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_extends_x3f_557_ = l_Lean_Syntax_getArg(v___x_552_, v___x_312_);
lean_dec(v___x_552_);
v___x_558_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__14));
lean_inc(v_extends_x3f_557_);
v___x_559_ = l_Lean_Syntax_isOfKind(v_extends_x3f_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_extends_x3f_557_);
lean_dec(v_type_x3f_548_);
lean_dec(v_typeAscriptionTk_x3f_547_);
lean_dec(v___x_397_);
lean_dec(v_configurationTk_325_);
lean_dec(v_declId_319_);
lean_dec(v_declModifiers_313_);
lean_dec(v_x_301_);
v___x_560_ = l_Lean_Fmt_Error_partialFormatter;
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___y_550_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v_extends_x3f_557_);
v___y_512_ = v_typeAscriptionTk_x3f_547_;
v___y_513_ = v_type_x3f_548_;
v_extends_x3f_514_ = v___x_562_;
v___y_515_ = v___y_549_;
v___y_516_ = v___y_550_;
goto v___jp_511_;
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v___x_552_);
v___x_563_ = lean_box(0);
v___y_512_ = v_typeAscriptionTk_x3f_547_;
v___y_513_ = v_type_x3f_548_;
v_extends_x3f_514_ = v___x_563_;
v___y_515_ = v___y_549_;
v___y_516_ = v___y_550_;
goto v___jp_511_;
}
}
}
}
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = l_Lean_Fmt_Error_partialFormatter;
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___y_305_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtConfigDecl___boxed(lean_object* v_x_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lake_Formatters_fmtConfigDecl(v_x_580_, v_a_581_, v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1(){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_590_ = l_Lean_Fmt_fmtAttribute;
v___x_591_ = ((lean_object*)(l_Lake_Formatters_fmtConfigDecl___closed__1));
v___x_592_ = ((lean_object*)(l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___closed__1));
v___x_593_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtConfigDecl___boxed), 3, 0);
v___x_594_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_590_, v___x_591_, v___x_592_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1___boxed(lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1();
return v_res_596_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Formatters_Config_Meta(uint8_t builtin) {
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
res = l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigField___regBuiltin_Lake_Formatters_fmtConfigField__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Config_Meta_0__Lake_Formatters_fmtConfigDecl___regBuiltin_Lake_Formatters_fmtConfigDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Formatters_Config_Meta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Formatters_Config_Meta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Formatters_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Formatters_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Formatters_Config_Meta(builtin);
}
#ifdef __cplusplus
}
#endif
