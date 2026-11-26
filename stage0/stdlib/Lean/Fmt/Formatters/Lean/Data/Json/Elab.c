// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Data.Json.Elab
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Data.Json.Elab import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_nl;
lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArrayLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtJsonTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtJsonTerm___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtJsonTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Json"};
static const lean_object* l_Lean_Fmt_fmtJsonTerm___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtJsonTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termJson%_"};
static const lean_object* l_Lean_Fmt_fmtJsonTerm___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonTerm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonTerm___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 92, 195, 143, 253, 86, 166, 134)}};
static const lean_object* l_Lean_Fmt_fmtJsonTerm___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonTerm___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtJsonTerm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 133, 7, 226, 192, 114, 2)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtJsonObject___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "json{_}"};
static const lean_object* l_Lean_Fmt_fmtJsonObject___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtJsonObject___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonObject___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonObject___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonObject___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonObject___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonObject___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtJsonObject___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 3, 125, 168, 133, 55, 242, 236)}};
static const lean_object* l_Lean_Fmt_fmtJsonObject___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtJsonObject___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtJsonObject___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtJsonObject___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtJsonObject___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_fmtJsonObject___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtJsonObject___closed__3;
static lean_once_cell_t l_Lean_Fmt_fmtJsonObject___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtJsonObject___closed__4;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonObject(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonObject___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtJsonObject"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 160, 64, 214, 131, 40, 220, 2)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtJsonField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "jsonField"};
static const lean_object* l_Lean_Fmt_fmtJsonField___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtJsonField___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonField___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonField___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonField___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonField___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtJsonField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 231, 71, 34, 65, 247, 44, 17)}};
static const lean_object* l_Lean_Fmt_fmtJsonField___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtJsonField___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtJsonField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "jsonIdent"};
static const lean_object* l_Lean_Fmt_fmtJsonField___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtJsonField___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonField___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonField___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonField___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonField___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtJsonField___closed__2_value),LEAN_SCALAR_PTR_LITERAL(100, 130, 95, 3, 148, 30, 174, 174)}};
static const lean_object* l_Lean_Fmt_fmtJsonField___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtJsonField___closed__3_value;
static const lean_closure_object l_Lean_Fmt_fmtJsonField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_nested, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtJsonField___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtJsonField___closed__4_value;
static lean_once_cell_t l_Lean_Fmt_fmtJsonField___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtJsonField___closed__5;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonField(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonField___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtJsonField"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 111, 31, 187, 180, 57, 182, 27)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtJsonIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtJsonIdent___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtJsonIdent___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonIdent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtJsonIdent___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtJsonIdent___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtJsonIdent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtJsonIdent___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtJsonIdent___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonIdent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonIdent___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtJsonIdent___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtJsonIdent___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonIdent___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtJsonIdent"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 149, 212, 245, 200, 95, 130, 214)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtJsonArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "json[_]"};
static const lean_object* l_Lean_Fmt_fmtJsonArray___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtJsonArray___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonArray___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonArray___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonArray___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonArray___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtJsonArray___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 228, 226, 42, 58, 91, 155, 101)}};
static const lean_object* l_Lean_Fmt_fmtJsonArray___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtJsonArray___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonArray___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtJsonArray"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 101, 62, 20, 147, 39, 159)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtJsonNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtJsonNum___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtJsonNum___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtJsonNum___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtJsonNum___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtJsonNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "json-_"};
static const lean_object* l_Lean_Fmt_fmtJsonNum___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtJsonNum___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonNum___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonNum___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonNum___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonNum___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtJsonNum___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 118, 11, 235, 35, 246, 227, 21)}};
static const lean_object* l_Lean_Fmt_fmtJsonNum___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtJsonNum___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonNum___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtJsonNum"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 222, 111, 142, 108, 86, 247, 57)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtJsonScientific___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_Fmt_fmtJsonScientific___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtJsonScientific___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonScientific___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonScientific___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_Fmt_fmtJsonScientific___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtJsonScientific___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtJsonScientific___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "json-__1"};
static const lean_object* l_Lean_Fmt_fmtJsonScientific___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtJsonScientific___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonScientific___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonScientific___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonScientific___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonScientific___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonScientific___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtJsonScientific___closed__2_value),LEAN_SCALAR_PTR_LITERAL(222, 117, 171, 240, 190, 70, 117, 11)}};
static const lean_object* l_Lean_Fmt_fmtJsonScientific___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtJsonScientific___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonScientific(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonScientific___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtJsonScientific"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 204, 227, 2, 14, 112, 53, 38)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtJsonStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "json_"};
static const lean_object* l_Lean_Fmt_fmtJsonStr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtJsonStr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtJsonStr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonStr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonStr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Fmt_fmtJsonStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtJsonStr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtJsonStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 121, 188, 241, 213, 216, 202, 40)}};
static const lean_object* l_Lean_Fmt_fmtJsonStr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtJsonStr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonStr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonStr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtJsonStr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtJsonTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 196, 150, 144, 152, 165, 127, 192)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonTerm(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_Fmt_fmtJsonTerm___closed__3));
lean_inc(v_x_8_);
v___x_12_ = l_Lean_Syntax_isOfKind(v_x_8_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_x_8_);
v___x_13_ = l_Lean_Fmt_Error_partialFormatter;
v___x_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_a_10_);
return v___x_14_;
}
else
{
lean_object* v___x_15_; lean_object* v_jsonTk_16_; lean_object* v___x_17_; 
v___x_15_ = lean_unsigned_to_nat(0u);
v_jsonTk_16_ = l_Lean_Syntax_getArg(v_x_8_, v___x_15_);
v___x_17_ = l_Lean_Fmt_fmt(v_jsonTk_16_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_17_, 2);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_8_, v___x_20_);
lean_dec(v_x_8_);
v___x_22_ = l_Lean_Fmt_fmt(v___x_21_, v_a_9_, v_a_19_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_38_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_a_24_ = lean_ctor_get(v___x_22_, 1);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_38_ == 0)
{
v___x_26_ = v___x_22_;
v_isShared_27_ = v_isSharedCheck_38_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_38_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_28_ = lean_unsigned_to_nat(2u);
v___x_29_ = lean_mk_empty_array_with_capacity(v___x_28_);
v___x_30_ = lean_array_push(v___x_29_, v_a_18_);
v___x_31_ = lean_array_push(v___x_30_, v_a_23_);
v___x_32_ = 0;
v___x_33_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_33_, 0, v___x_12_);
lean_ctor_set_uint8(v___x_33_, 1, v___x_32_);
lean_ctor_set_uint8(v___x_33_, 2, v___x_32_);
lean_ctor_set_uint8(v___x_33_, 3, v___x_32_);
v___x_34_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_31_, v___x_33_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_34_);
v___x_36_ = v___x_26_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_a_24_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_dec(v_a_18_);
return v___x_22_;
}
}
else
{
lean_dec(v_x_8_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonTerm___boxed(lean_object* v_x_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Fmt_fmtJsonTerm(v_x_39_, v_a_40_, v_a_41_);
lean_dec_ref(v_a_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_50_ = l_Lean_Fmt_fmtAttribute;
v___x_51_ = ((lean_object*)(l_Lean_Fmt_fmtJsonTerm___closed__3));
v___x_52_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___closed__2));
v___x_53_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtJsonTerm___boxed), 3, 0);
v___x_54_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_50_, v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1___boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1();
return v_res_56_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtJsonObject___closed__3(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtJsonObject___closed__4(void){
_start:
{
uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = 1;
v___x_66_ = lean_obj_once(&l_Lean_Fmt_fmtJsonObject___closed__3, &l_Lean_Fmt_fmtJsonObject___closed__3_once, _init_l_Lean_Fmt_fmtJsonObject___closed__3);
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*2, v___x_65_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonObject(lean_object* v_x_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = ((lean_object*)(l_Lean_Fmt_fmtJsonObject___closed__1));
lean_inc(v_x_69_);
v___x_73_ = l_Lean_Syntax_isOfKind(v_x_69_, v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_x_69_);
v___x_74_ = l_Lean_Fmt_Error_partialFormatter;
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v_a_71_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v_lbTk_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v_lbTk_77_ = l_Lean_Syntax_getArg(v_x_69_, v___x_76_);
v___x_78_ = l_Lean_Fmt_fmt(v_lbTk_77_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v_a_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v_fields_83_; lean_object* v___x_84_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
v_a_80_ = lean_ctor_get(v___x_78_, 1);
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_78_, 2);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = l_Lean_Syntax_getArg(v_x_69_, v___x_81_);
v_fields_83_ = l_Lean_Syntax_getArgs(v___x_82_);
lean_dec(v___x_82_);
v___x_84_ = l_Lean_Fmt_fmtTSepArray___redArg(v_fields_83_, v_a_70_, v_a_80_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v_a_86_; lean_object* v___x_87_; lean_object* v_rbTk_88_; lean_object* v___x_89_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
v_a_86_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_a_86_);
lean_dec_ref_known(v___x_84_, 2);
v___x_87_ = lean_unsigned_to_nat(2u);
v_rbTk_88_ = l_Lean_Syntax_getArg(v_x_69_, v___x_87_);
lean_dec(v_x_69_);
v___x_89_ = l_Lean_Fmt_fmt(v_rbTk_88_, v_a_70_, v_a_86_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_105_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_a_91_ = lean_ctor_get(v___x_89_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_105_ == 0)
{
v___x_93_ = v___x_89_;
v_isShared_94_ = v_isSharedCheck_105_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_105_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_95_ = ((lean_object*)(l_Lean_Fmt_fmtJsonObject___closed__2));
v___x_96_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_97_ = lean_obj_once(&l_Lean_Fmt_fmtJsonObject___closed__4, &l_Lean_Fmt_fmtJsonObject___closed__4_once, _init_l_Lean_Fmt_fmtJsonObject___closed__4);
v___x_98_ = l_Lean_Fmt_Layouts_sepArray(v___x_95_, v_a_85_, v___x_97_);
lean_dec(v_a_85_);
v___x_99_ = 1;
v___x_100_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_100_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_73_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1 + 1, v___x_99_);
v___x_101_ = l_Lean_Fmt_Layouts_bracketed(v_a_79_, v___x_98_, v_a_90_, v___x_100_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_101_);
v___x_103_ = v___x_93_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_a_91_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
else
{
lean_dec(v_a_85_);
lean_dec(v_a_79_);
return v___x_89_;
}
}
else
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_dec(v_a_79_);
lean_dec(v_x_69_);
v_a_106_ = lean_ctor_get(v___x_84_, 0);
v_a_107_ = lean_ctor_get(v___x_84_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_84_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_inc(v_a_106_);
lean_dec(v___x_84_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_106_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_dec(v_x_69_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonObject___boxed(lean_object* v_x_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Fmt_fmtJsonObject(v_x_115_, v_a_116_, v_a_117_);
lean_dec_ref(v_a_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1(){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = l_Lean_Fmt_fmtAttribute;
v___x_126_ = ((lean_object*)(l_Lean_Fmt_fmtJsonObject___closed__1));
v___x_127_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___closed__1));
v___x_128_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtJsonObject___boxed), 3, 0);
v___x_129_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_125_, v___x_126_, v___x_127_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1___boxed(lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1();
return v_res_131_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtJsonField___closed__5(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = ((lean_object*)(l_Lean_Fmt_fmtJsonField___closed__4));
v___x_144_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonField(lean_object* v_x_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_Fmt_fmtJsonField___closed__1));
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
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_Syntax_getArg(v_x_146_, v___x_153_);
v___x_155_ = ((lean_object*)(l_Lean_Fmt_fmtJsonField___closed__3));
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
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Fmt_fmt(v___x_154_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v_colonTk_163_; lean_object* v___x_164_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
v_a_161_ = lean_ctor_get(v___x_159_, 1);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_159_, 2);
v___x_162_ = lean_unsigned_to_nat(1u);
v_colonTk_163_ = l_Lean_Syntax_getArg(v_x_146_, v___x_162_);
v___x_164_ = l_Lean_Fmt_fmt(v_colonTk_163_, v_a_147_, v_a_161_);
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
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_175_ = l_Lean_Fmt_TaggedDoc_hardNested(v_a_160_);
v___x_176_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_177_ = lean_array_push(v___x_176_, v___x_175_);
v___x_178_ = lean_array_push(v___x_177_, v_a_165_);
v___x_179_ = l_Lean_Fmt_Layouts_atomic(v___x_178_);
lean_dec_ref(v___x_178_);
v___x_180_ = lean_obj_once(&l_Lean_Fmt_fmtJsonField___closed__5, &l_Lean_Fmt_fmtJsonField___closed__5_once, _init_l_Lean_Fmt_fmtJsonField___closed__5);
v___x_181_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_179_, v___x_180_, v_a_170_, v___x_156_);
v___x_182_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_181_);
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
lean_dec(v_a_160_);
return v___x_169_;
}
}
else
{
lean_dec(v_a_160_);
lean_dec(v_x_146_);
return v___x_164_;
}
}
else
{
lean_dec(v_x_146_);
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonField___boxed(lean_object* v_x_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Fmt_fmtJsonField(v_x_187_, v_a_188_, v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1(){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = l_Lean_Fmt_fmtAttribute;
v___x_198_ = ((lean_object*)(l_Lean_Fmt_fmtJsonField___closed__1));
v___x_199_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___closed__1));
v___x_200_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtJsonField___boxed), 3, 0);
v___x_201_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_197_, v___x_198_, v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1___boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1();
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonIdent(lean_object* v_x_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Fmt_fmtJsonField___closed__3));
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
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = l_Lean_Syntax_getArg(v_x_210_, v___x_217_);
lean_dec(v_x_210_);
v___x_219_ = ((lean_object*)(l_Lean_Fmt_fmtJsonIdent___closed__1));
lean_inc(v___x_218_);
v___x_220_ = l_Lean_Syntax_isOfKind(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Fmt_fmtJsonIdent___closed__3));
lean_inc(v___x_218_);
v___x_222_ = l_Lean_Syntax_isOfKind(v___x_218_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v___x_218_);
v___x_223_ = l_Lean_Fmt_Error_partialFormatter;
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v_a_212_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Fmt_fmt(v___x_218_, v_a_211_, v_a_212_);
return v___x_225_;
}
}
else
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Fmt_fmt(v___x_218_, v_a_211_, v_a_212_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonIdent___boxed(lean_object* v_x_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Fmt_fmtJsonIdent(v_x_227_, v_a_228_, v_a_229_);
lean_dec_ref(v_a_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1(){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_237_ = l_Lean_Fmt_fmtAttribute;
v___x_238_ = ((lean_object*)(l_Lean_Fmt_fmtJsonField___closed__3));
v___x_239_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___closed__1));
v___x_240_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtJsonIdent___boxed), 3, 0);
v___x_241_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_237_, v___x_238_, v___x_239_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1___boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1();
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonArray(lean_object* v_x_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lean_Fmt_fmtJsonArray___closed__1));
lean_inc(v_x_249_);
v___x_253_ = l_Lean_Syntax_isOfKind(v_x_249_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_x_249_);
v___x_254_ = l_Lean_Fmt_Error_partialFormatter;
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_251_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v_lbTk_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_rbTk_261_; lean_object* v_elems_262_; lean_object* v___x_263_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v_lbTk_257_ = l_Lean_Syntax_getArg(v_x_249_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_249_, v___x_258_);
v___x_260_ = lean_unsigned_to_nat(2u);
v_rbTk_261_ = l_Lean_Syntax_getArg(v_x_249_, v___x_260_);
lean_dec(v_x_249_);
v_elems_262_ = l_Lean_Syntax_getArgs(v___x_259_);
lean_dec(v___x_259_);
v___x_263_ = l_Lean_Fmt_fmtArrayLit___redArg(v_lbTk_257_, v_elems_262_, v_rbTk_261_, v_a_250_, v_a_251_);
lean_dec_ref(v_elems_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonArray___boxed(lean_object* v_x_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Fmt_fmtJsonArray(v_x_264_, v_a_265_, v_a_266_);
lean_dec_ref(v_a_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1(){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_274_ = l_Lean_Fmt_fmtAttribute;
v___x_275_ = ((lean_object*)(l_Lean_Fmt_fmtJsonArray___closed__1));
v___x_276_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___closed__1));
v___x_277_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtJsonArray___boxed), 3, 0);
v___x_278_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_274_, v___x_275_, v___x_276_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1___boxed(lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1();
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonNum(lean_object* v_x_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_minusTk_x3f_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Fmt_fmtJsonNum___closed__3));
lean_inc(v_x_289_);
v___x_318_ = l_Lean_Syntax_isOfKind(v_x_289_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_x_289_);
v___x_319_ = l_Lean_Fmt_Error_partialFormatter;
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_a_291_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Lean_Syntax_getArg(v_x_289_, v___x_321_);
v___x_323_ = l_Lean_Syntax_isNone(v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_322_);
v___x_325_ = l_Lean_Syntax_matchesNull(v___x_322_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v___x_322_);
lean_dec(v_x_289_);
v___x_326_ = l_Lean_Fmt_Error_partialFormatter;
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_a_291_);
return v___x_327_;
}
else
{
lean_object* v_minusTk_x3f_328_; lean_object* v___x_329_; 
v_minusTk_x3f_328_ = l_Lean_Syntax_getArg(v___x_322_, v___x_321_);
lean_dec(v___x_322_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_minusTk_x3f_328_);
v_minusTk_x3f_293_ = v___x_329_;
v___y_294_ = v_a_290_;
v___y_295_ = v_a_291_;
goto v___jp_292_;
}
}
else
{
lean_object* v___x_330_; 
lean_dec(v___x_322_);
v___x_330_ = lean_box(0);
v_minusTk_x3f_293_ = v___x_330_;
v___y_294_ = v_a_290_;
v___y_295_ = v_a_291_;
goto v___jp_292_;
}
}
v___jp_292_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = l_Lean_Syntax_getArg(v_x_289_, v___x_296_);
lean_dec(v_x_289_);
v___x_298_ = ((lean_object*)(l_Lean_Fmt_fmtJsonNum___closed__1));
lean_inc(v___x_297_);
v___x_299_ = l_Lean_Syntax_isOfKind(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v___x_297_);
lean_dec(v_minusTk_x3f_293_);
v___x_300_ = l_Lean_Fmt_Error_partialFormatter;
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___y_295_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Fmt_fmt_x3f(v_minusTk_x3f_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v_a_304_; lean_object* v___x_305_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
v_a_304_ = lean_ctor_get(v___x_302_, 1);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_302_, 2);
v___x_305_ = l_Lean_Fmt_fmt(v___x_297_, v___y_294_, v_a_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_316_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_a_307_ = lean_ctor_get(v___x_305_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_316_ == 0)
{
v___x_309_ = v___x_305_;
v_isShared_310_ = v_isSharedCheck_316_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_316_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_311_ = 0;
v___x_312_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_303_, v_a_306_, v___x_311_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_312_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_a_307_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_dec(v_a_303_);
return v___x_305_;
}
}
else
{
lean_dec(v___x_297_);
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonNum___boxed(lean_object* v_x_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Fmt_fmtJsonNum(v_x_331_, v_a_332_, v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1(){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_341_ = l_Lean_Fmt_fmtAttribute;
v___x_342_ = ((lean_object*)(l_Lean_Fmt_fmtJsonNum___closed__3));
v___x_343_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___closed__1));
v___x_344_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtJsonNum___boxed), 3, 0);
v___x_345_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_341_, v___x_342_, v___x_343_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1___boxed(lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1();
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonScientific(lean_object* v_x_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_minusTk_x3f_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Fmt_fmtJsonScientific___closed__3));
lean_inc(v_x_356_);
v___x_385_ = l_Lean_Syntax_isOfKind(v_x_356_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v_x_356_);
v___x_386_ = l_Lean_Fmt_Error_partialFormatter;
v___x_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_a_358_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = l_Lean_Syntax_getArg(v_x_356_, v___x_388_);
v___x_390_ = l_Lean_Syntax_isNone(v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_389_);
v___x_392_ = l_Lean_Syntax_matchesNull(v___x_389_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v___x_389_);
lean_dec(v_x_356_);
v___x_393_ = l_Lean_Fmt_Error_partialFormatter;
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v_a_358_);
return v___x_394_;
}
else
{
lean_object* v_minusTk_x3f_395_; lean_object* v___x_396_; 
v_minusTk_x3f_395_ = l_Lean_Syntax_getArg(v___x_389_, v___x_388_);
lean_dec(v___x_389_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_minusTk_x3f_395_);
v_minusTk_x3f_360_ = v___x_396_;
v___y_361_ = v_a_357_;
v___y_362_ = v_a_358_;
goto v___jp_359_;
}
}
else
{
lean_object* v___x_397_; 
lean_dec(v___x_389_);
v___x_397_ = lean_box(0);
v_minusTk_x3f_360_ = v___x_397_;
v___y_361_ = v_a_357_;
v___y_362_ = v_a_358_;
goto v___jp_359_;
}
}
v___jp_359_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = l_Lean_Syntax_getArg(v_x_356_, v___x_363_);
lean_dec(v_x_356_);
v___x_365_ = ((lean_object*)(l_Lean_Fmt_fmtJsonScientific___closed__1));
lean_inc(v___x_364_);
v___x_366_ = l_Lean_Syntax_isOfKind(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec(v___x_364_);
lean_dec(v_minusTk_x3f_360_);
v___x_367_ = l_Lean_Fmt_Error_partialFormatter;
v___x_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___y_362_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Fmt_fmt_x3f(v_minusTk_x3f_360_, v___y_361_, v___y_362_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v_a_371_; lean_object* v___x_372_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
v_a_371_ = lean_ctor_get(v___x_369_, 1);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_369_, 2);
v___x_372_ = l_Lean_Fmt_fmt(v___x_364_, v___y_361_, v_a_371_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_383_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_a_374_ = lean_ctor_get(v___x_372_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_383_ == 0)
{
v___x_376_ = v___x_372_;
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_378_ = 0;
v___x_379_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_370_, v_a_373_, v___x_378_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_379_);
v___x_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_a_374_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_dec(v_a_370_);
return v___x_372_;
}
}
else
{
lean_dec(v___x_364_);
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonScientific___boxed(lean_object* v_x_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Fmt_fmtJsonScientific(v_x_398_, v_a_399_, v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1(){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_408_ = l_Lean_Fmt_fmtAttribute;
v___x_409_ = ((lean_object*)(l_Lean_Fmt_fmtJsonScientific___closed__3));
v___x_410_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___closed__1));
v___x_411_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtJsonScientific___boxed), 3, 0);
v___x_412_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_408_, v___x_409_, v___x_410_, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1___boxed(lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1();
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonStr(lean_object* v_x_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Fmt_fmtJsonStr___closed__1));
lean_inc(v_x_420_);
v___x_424_ = l_Lean_Syntax_isOfKind(v_x_420_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_x_420_);
v___x_425_ = l_Lean_Fmt_Error_partialFormatter;
v___x_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_a_422_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = l_Lean_Syntax_getArg(v_x_420_, v___x_427_);
lean_dec(v_x_420_);
v___x_429_ = ((lean_object*)(l_Lean_Fmt_fmtJsonIdent___closed__3));
lean_inc(v___x_428_);
v___x_430_ = l_Lean_Syntax_isOfKind(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v___x_428_);
v___x_431_ = l_Lean_Fmt_Error_partialFormatter;
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_a_422_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Fmt_fmt(v___x_428_, v_a_421_, v_a_422_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtJsonStr___boxed(lean_object* v_x_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Fmt_fmtJsonStr(v_x_434_, v_a_435_, v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1(){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_444_ = l_Lean_Fmt_fmtAttribute;
v___x_445_ = ((lean_object*)(l_Lean_Fmt_fmtJsonStr___closed__1));
v___x_446_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___closed__1));
v___x_447_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtJsonStr___boxed), 3, 0);
v___x_448_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_444_, v___x_445_, v___x_446_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1___boxed(lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1();
return v_res_450_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Data_Json_Elab(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonTerm___regBuiltin_Lean_Fmt_fmtJsonTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonObject___regBuiltin_Lean_Fmt_fmtJsonObject__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonField___regBuiltin_Lean_Fmt_fmtJsonField__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonIdent___regBuiltin_Lean_Fmt_fmtJsonIdent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonArray___regBuiltin_Lean_Fmt_fmtJsonArray__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonNum___regBuiltin_Lean_Fmt_fmtJsonNum__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonScientific___regBuiltin_Lean_Fmt_fmtJsonScientific__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Json_Elab_0__Lean_Fmt_fmtJsonStr___regBuiltin_Lean_Fmt_fmtJsonStr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Data_Json_Elab(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Data_Json_Elab(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Data_Json_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_Elab(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Data_Json_Elab(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Data_Json_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Data_Json_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Data_Json_Elab(builtin);
}
#ifdef __cplusplus
}
#endif
