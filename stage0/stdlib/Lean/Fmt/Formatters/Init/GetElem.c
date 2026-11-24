// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.GetElem
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.GetElem import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGetElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__[_]"};
static const lean_object* l_Lean_Fmt_fmtGetElem___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGetElem___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGetElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGetElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 146, 84, 128, 183, 70, 246)}};
static const lean_object* l_Lean_Fmt_fmtGetElem___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGetElem___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElem___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtGetElem"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 8, 143, 217, 49, 17, 212, 165)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGetElemQuestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]_\?"};
static const lean_object* l_Lean_Fmt_fmtGetElemQuestion___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGetElemQuestion___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGetElemQuestion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGetElemQuestion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 178, 109, 68, 161, 229, 23, 17)}};
static const lean_object* l_Lean_Fmt_fmtGetElemQuestion___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGetElemQuestion___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGetElemQuestion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Fmt_fmtGetElemQuestion___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGetElemQuestion___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGetElemQuestion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGetElemQuestion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Fmt_fmtGetElemQuestion___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGetElemQuestion___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemQuestion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemQuestion___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtGetElemQuestion"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 40, 100, 211, 245, 107, 245, 58)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGetElemExclamation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]_!"};
static const lean_object* l_Lean_Fmt_fmtGetElemExclamation___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGetElemExclamation___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGetElemExclamation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGetElemExclamation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 145, 92, 47, 59, 8, 18, 13)}};
static const lean_object* l_Lean_Fmt_fmtGetElemExclamation___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGetElemExclamation___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemExclamation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemExclamation___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtGetElemExclamation"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 161, 131, 253, 189, 203, 160, 236)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGetElemProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]'_"};
static const lean_object* l_Lean_Fmt_fmtGetElemProof___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGetElemProof___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGetElemProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGetElemProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 98, 175, 4, 199, 28, 246, 201)}};
static const lean_object* l_Lean_Fmt_fmtGetElemProof___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGetElemProof___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemProof(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemProof___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGetElemProof"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 141, 105, 237, 75, 49, 81, 213)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElem(lean_object* v_x_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Fmt_fmtGetElem___closed__1));
lean_inc(v_x_4_);
v___x_8_ = l_Lean_Syntax_isOfKind(v_x_4_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_x_4_);
v___x_9_ = l_Lean_Fmt_Error_partialFormatter;
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v_a_6_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = l_Lean_Syntax_getArg(v_x_4_, v___x_11_);
v___x_13_ = l_Lean_Fmt_fmt(v___x_12_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v_a_15_; lean_object* v___x_16_; lean_object* v_lbTk_17_; lean_object* v___x_18_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
v_a_15_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_a_15_);
lean_dec_ref_known(v___x_13_, 2);
v___x_16_ = lean_unsigned_to_nat(1u);
v_lbTk_17_ = l_Lean_Syntax_getArg(v_x_4_, v___x_16_);
v___x_18_ = l_Lean_Fmt_fmt(v_lbTk_17_, v_a_5_, v_a_15_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v_a_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
v_a_20_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_18_, 2);
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = l_Lean_Syntax_getArg(v_x_4_, v___x_21_);
v___x_23_ = l_Lean_Fmt_fmt(v___x_22_, v_a_5_, v_a_20_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v_a_25_; lean_object* v___x_26_; lean_object* v_rbTk_27_; lean_object* v___x_28_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
v_a_25_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_a_25_);
lean_dec_ref_known(v___x_23_, 2);
v___x_26_ = lean_unsigned_to_nat(3u);
v_rbTk_27_ = l_Lean_Syntax_getArg(v_x_4_, v___x_26_);
lean_dec(v_x_4_);
v___x_28_ = l_Lean_Fmt_fmt(v_rbTk_27_, v_a_5_, v_a_25_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_45_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_45_ == 0)
{
v___x_32_ = v___x_28_;
v_isShared_33_ = v_isSharedCheck_45_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_45_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_34_ = 0;
v___x_35_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_35_, 0, v___x_34_);
lean_ctor_set_uint8(v___x_35_, 1, v___x_8_);
v___x_36_ = l_Lean_Fmt_Layouts_bracketed(v_a_19_, v_a_24_, v_a_29_, v___x_35_);
v___x_37_ = lean_mk_empty_array_with_capacity(v___x_21_);
v___x_38_ = lean_array_push(v___x_37_, v_a_14_);
v___x_39_ = lean_array_push(v___x_38_, v___x_36_);
v___x_40_ = l_Lean_Fmt_Layouts_atomic(v___x_39_);
lean_dec_ref(v___x_39_);
v___x_41_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_40_, v___x_34_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_41_);
v___x_43_ = v___x_32_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_a_30_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
else
{
lean_dec(v_a_24_);
lean_dec(v_a_19_);
lean_dec(v_a_14_);
return v___x_28_;
}
}
else
{
lean_dec(v_a_19_);
lean_dec(v_a_14_);
lean_dec(v_x_4_);
return v___x_23_;
}
}
else
{
lean_dec(v_a_14_);
lean_dec(v_x_4_);
return v___x_18_;
}
}
else
{
lean_dec(v_x_4_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElem___boxed(lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Fmt_fmtGetElem(v_x_46_, v_a_47_, v_a_48_);
lean_dec_ref(v_a_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_58_ = l_Lean_Fmt_fmtAttribute;
v___x_59_ = ((lean_object*)(l_Lean_Fmt_fmtGetElem___closed__1));
v___x_60_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___closed__3));
v___x_61_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGetElem___boxed), 3, 0);
v___x_62_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_58_, v___x_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1___boxed(lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1();
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemQuestion(lean_object* v_stx_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = ((lean_object*)(l_Lean_Fmt_fmtGetElemQuestion___closed__1));
lean_inc(v_stx_71_);
v___x_75_ = l_Lean_Syntax_isOfKind(v_stx_71_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v_stx_71_);
v___x_76_ = l_Lean_Fmt_Error_partialFormatter;
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_a_73_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = l_Lean_Syntax_getArg(v_stx_71_, v___x_78_);
v___x_80_ = ((lean_object*)(l_Lean_Fmt_fmtGetElemQuestion___closed__3));
v___x_81_ = l_Lean_Syntax_isOfKind(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_stx_71_);
v___x_82_ = l_Lean_Fmt_Error_partialFormatter;
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_a_73_);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_unsigned_to_nat(5u);
v___x_85_ = l_Lean_Syntax_getArg(v_stx_71_, v___x_84_);
v___x_86_ = l_Lean_Syntax_isOfKind(v___x_85_, v___x_80_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_stx_71_);
v___x_87_ = l_Lean_Fmt_Error_partialFormatter;
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_a_73_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(4u);
v___x_90_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_71_, v___x_89_, v_a_73_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v___x_90_, 1);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_90_, 2);
v___x_93_ = lean_unsigned_to_nat(6u);
v___x_94_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_71_, v___x_93_, v_a_92_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
v_a_96_ = lean_ctor_get(v___x_94_, 1);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_94_, 2);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = l_Lean_Syntax_getArg(v_stx_71_, v___x_97_);
v___x_99_ = l_Lean_Fmt_fmt(v___x_98_, v_a_72_, v_a_96_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v___x_102_; lean_object* v_lbTk_103_; lean_object* v___x_104_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v_a_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_99_, 2);
v___x_102_ = lean_unsigned_to_nat(2u);
v_lbTk_103_ = l_Lean_Syntax_getArg(v_stx_71_, v___x_102_);
v___x_104_ = l_Lean_Fmt_fmt(v_lbTk_103_, v_a_72_, v_a_101_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v_a_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
v_a_106_ = lean_ctor_get(v___x_104_, 1);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_104_, 2);
v___x_107_ = lean_unsigned_to_nat(3u);
v___x_108_ = l_Lean_Syntax_getArg(v_stx_71_, v___x_107_);
lean_dec(v_stx_71_);
v___x_109_ = l_Lean_Fmt_fmt(v___x_108_, v_a_72_, v_a_106_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v_a_111_; lean_object* v___x_112_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
v_a_111_ = lean_ctor_get(v___x_109_, 1);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_109_, 2);
v___x_112_ = l_Lean_Fmt_fmt(v_a_91_, v_a_72_, v_a_111_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v___x_115_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
v_a_114_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_112_, 2);
v___x_115_ = l_Lean_Fmt_fmt(v_a_95_, v_a_72_, v_a_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_133_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_a_117_ = lean_ctor_get(v___x_115_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_133_ == 0)
{
v___x_119_ = v___x_115_;
v_isShared_120_ = v_isSharedCheck_133_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_133_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_121_ = 0;
v___x_122_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_122_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_122_, 1, v___x_86_);
v___x_123_ = l_Lean_Fmt_Layouts_bracketed(v_a_105_, v_a_110_, v_a_113_, v___x_122_);
v___x_124_ = lean_mk_empty_array_with_capacity(v___x_107_);
v___x_125_ = lean_array_push(v___x_124_, v_a_100_);
v___x_126_ = lean_array_push(v___x_125_, v___x_123_);
v___x_127_ = lean_array_push(v___x_126_, v_a_116_);
v___x_128_ = l_Lean_Fmt_Layouts_atomic(v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_128_, v___x_121_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_129_);
v___x_131_ = v___x_119_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_a_117_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_dec(v_a_113_);
lean_dec(v_a_110_);
lean_dec(v_a_105_);
lean_dec(v_a_100_);
return v___x_115_;
}
}
else
{
lean_dec(v_a_110_);
lean_dec(v_a_105_);
lean_dec(v_a_100_);
lean_dec(v_a_95_);
return v___x_112_;
}
}
else
{
lean_dec(v_a_105_);
lean_dec(v_a_100_);
lean_dec(v_a_95_);
lean_dec(v_a_91_);
return v___x_109_;
}
}
else
{
lean_dec(v_a_100_);
lean_dec(v_a_95_);
lean_dec(v_a_91_);
lean_dec(v_stx_71_);
return v___x_104_;
}
}
else
{
lean_dec(v_a_95_);
lean_dec(v_a_91_);
lean_dec(v_stx_71_);
return v___x_99_;
}
}
else
{
lean_object* v_a_134_; lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_dec(v_a_91_);
lean_dec(v_stx_71_);
v_a_134_ = lean_ctor_get(v___x_94_, 0);
v_a_135_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_94_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_inc(v_a_134_);
lean_dec(v___x_94_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_134_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
else
{
lean_object* v_a_143_; lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_stx_71_);
v_a_143_ = lean_ctor_get(v___x_90_, 0);
v_a_144_ = lean_ctor_get(v___x_90_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_90_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_inc(v_a_143_);
lean_dec(v___x_90_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_143_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemQuestion___boxed(lean_object* v_stx_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Fmt_fmtGetElemQuestion(v_stx_152_, v_a_153_, v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1(){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_162_ = l_Lean_Fmt_fmtAttribute;
v___x_163_ = ((lean_object*)(l_Lean_Fmt_fmtGetElemQuestion___closed__1));
v___x_164_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___closed__1));
v___x_165_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGetElemQuestion___boxed), 3, 0);
v___x_166_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_162_, v___x_163_, v___x_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1___boxed(lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1();
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemExclamation(lean_object* v_stx_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Fmt_fmtGetElemExclamation___closed__1));
lean_inc(v_stx_172_);
v___x_176_ = l_Lean_Syntax_isOfKind(v_stx_172_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_stx_172_);
v___x_177_ = l_Lean_Fmt_Error_partialFormatter;
v___x_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_a_174_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_179_);
v___x_181_ = ((lean_object*)(l_Lean_Fmt_fmtGetElemQuestion___closed__3));
v___x_182_ = l_Lean_Syntax_isOfKind(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_stx_172_);
v___x_183_ = l_Lean_Fmt_Error_partialFormatter;
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_174_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = lean_unsigned_to_nat(5u);
v___x_186_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_185_);
v___x_187_ = l_Lean_Syntax_isOfKind(v___x_186_, v___x_181_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_stx_172_);
v___x_188_ = l_Lean_Fmt_Error_partialFormatter;
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_174_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(4u);
v___x_191_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_172_, v___x_190_, v_a_174_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v_a_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
v_a_193_ = lean_ctor_get(v___x_191_, 1);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_191_, 2);
v___x_194_ = lean_unsigned_to_nat(6u);
v___x_195_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_172_, v___x_194_, v_a_193_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v_a_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
v_a_197_ = lean_ctor_get(v___x_195_, 1);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_195_, 2);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_198_);
v___x_200_ = l_Lean_Fmt_fmt(v___x_199_, v_a_173_, v_a_197_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_a_202_; lean_object* v___x_203_; lean_object* v_lbTk_204_; lean_object* v___x_205_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
v_a_202_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_200_, 2);
v___x_203_ = lean_unsigned_to_nat(2u);
v_lbTk_204_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_203_);
v___x_205_ = l_Lean_Fmt_fmt(v_lbTk_204_, v_a_173_, v_a_202_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v_a_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
v_a_207_ = lean_ctor_get(v___x_205_, 1);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_205_, 2);
v___x_208_ = lean_unsigned_to_nat(3u);
v___x_209_ = l_Lean_Syntax_getArg(v_stx_172_, v___x_208_);
lean_dec(v_stx_172_);
v___x_210_ = l_Lean_Fmt_fmt(v___x_209_, v_a_173_, v_a_207_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
v_a_212_ = lean_ctor_get(v___x_210_, 1);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_210_, 2);
v___x_213_ = l_Lean_Fmt_fmt(v_a_192_, v_a_173_, v_a_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
v_a_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_213_, 2);
v___x_216_ = l_Lean_Fmt_fmt(v_a_196_, v_a_173_, v_a_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_234_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_a_218_ = lean_ctor_get(v___x_216_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_234_ == 0)
{
v___x_220_ = v___x_216_;
v_isShared_221_ = v_isSharedCheck_234_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_234_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_222_ = 0;
v___x_223_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_223_, 0, v___x_222_);
lean_ctor_set_uint8(v___x_223_, 1, v___x_187_);
v___x_224_ = l_Lean_Fmt_Layouts_bracketed(v_a_206_, v_a_211_, v_a_214_, v___x_223_);
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_208_);
v___x_226_ = lean_array_push(v___x_225_, v_a_201_);
v___x_227_ = lean_array_push(v___x_226_, v___x_224_);
v___x_228_ = lean_array_push(v___x_227_, v_a_217_);
v___x_229_ = l_Lean_Fmt_Layouts_atomic(v___x_228_);
lean_dec_ref(v___x_228_);
v___x_230_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_229_, v___x_222_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_230_);
v___x_232_ = v___x_220_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_a_218_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
else
{
lean_dec(v_a_214_);
lean_dec(v_a_211_);
lean_dec(v_a_206_);
lean_dec(v_a_201_);
return v___x_216_;
}
}
else
{
lean_dec(v_a_211_);
lean_dec(v_a_206_);
lean_dec(v_a_201_);
lean_dec(v_a_196_);
return v___x_213_;
}
}
else
{
lean_dec(v_a_206_);
lean_dec(v_a_201_);
lean_dec(v_a_196_);
lean_dec(v_a_192_);
return v___x_210_;
}
}
else
{
lean_dec(v_a_201_);
lean_dec(v_a_196_);
lean_dec(v_a_192_);
lean_dec(v_stx_172_);
return v___x_205_;
}
}
else
{
lean_dec(v_a_196_);
lean_dec(v_a_192_);
lean_dec(v_stx_172_);
return v___x_200_;
}
}
else
{
lean_object* v_a_235_; lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_a_192_);
lean_dec(v_stx_172_);
v_a_235_ = lean_ctor_get(v___x_195_, 0);
v_a_236_ = lean_ctor_get(v___x_195_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_195_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_inc(v_a_235_);
lean_dec(v___x_195_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_235_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec(v_stx_172_);
v_a_244_ = lean_ctor_get(v___x_191_, 0);
v_a_245_ = lean_ctor_get(v___x_191_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_191_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_inc(v_a_244_);
lean_dec(v___x_191_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_244_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemExclamation___boxed(lean_object* v_stx_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Fmt_fmtGetElemExclamation(v_stx_253_, v_a_254_, v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1(){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = l_Lean_Fmt_fmtAttribute;
v___x_264_ = ((lean_object*)(l_Lean_Fmt_fmtGetElemExclamation___closed__1));
v___x_265_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___closed__1));
v___x_266_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGetElemExclamation___boxed), 3, 0);
v___x_267_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_263_, v___x_264_, v___x_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1___boxed(lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemProof(lean_object* v_x_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_Fmt_fmtGetElemProof___closed__1));
lean_inc(v_x_273_);
v___x_277_ = l_Lean_Syntax_isOfKind(v_x_273_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_x_273_);
v___x_278_ = l_Lean_Fmt_Error_partialFormatter;
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_a_275_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = l_Lean_Syntax_getArg(v_x_273_, v___x_280_);
v___x_282_ = l_Lean_Fmt_fmt(v___x_281_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v_lbTk_286_; lean_object* v___x_287_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
v_a_284_ = lean_ctor_get(v___x_282_, 1);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_282_, 2);
v___x_285_ = lean_unsigned_to_nat(1u);
v_lbTk_286_ = l_Lean_Syntax_getArg(v_x_273_, v___x_285_);
v___x_287_ = l_Lean_Fmt_fmt(v_lbTk_286_, v_a_274_, v_a_284_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v_a_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
v_a_289_ = lean_ctor_get(v___x_287_, 1);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_287_, 2);
v___x_290_ = lean_unsigned_to_nat(2u);
v___x_291_ = l_Lean_Syntax_getArg(v_x_273_, v___x_290_);
v___x_292_ = l_Lean_Fmt_fmt(v___x_291_, v_a_274_, v_a_289_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v_rbTk_296_; lean_object* v___x_297_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
v_a_294_ = lean_ctor_get(v___x_292_, 1);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_292_, 2);
v___x_295_ = lean_unsigned_to_nat(3u);
v_rbTk_296_ = l_Lean_Syntax_getArg(v_x_273_, v___x_295_);
v___x_297_ = l_Lean_Fmt_fmt(v_rbTk_296_, v_a_274_, v_a_294_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v_a_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
v_a_299_ = lean_ctor_get(v___x_297_, 1);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_297_, 2);
v___x_300_ = lean_unsigned_to_nat(4u);
v___x_301_ = l_Lean_Syntax_getArg(v_x_273_, v___x_300_);
lean_dec(v_x_273_);
v___x_302_ = l_Lean_Fmt_fmt(v___x_301_, v_a_274_, v_a_299_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_322_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_a_304_ = lean_ctor_get(v___x_302_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_322_ == 0)
{
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_322_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_322_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_308_ = 0;
v___x_309_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_309_, 0, v___x_308_);
lean_ctor_set_uint8(v___x_309_, 1, v___x_277_);
v___x_310_ = l_Lean_Fmt_Layouts_bracketed(v_a_288_, v_a_293_, v_a_298_, v___x_309_);
v___x_311_ = lean_mk_empty_array_with_capacity(v___x_290_);
lean_inc_ref(v___x_311_);
v___x_312_ = lean_array_push(v___x_311_, v_a_283_);
v___x_313_ = lean_array_push(v___x_312_, v___x_310_);
v___x_314_ = l_Lean_Fmt_Layouts_atomic(v___x_313_);
lean_dec_ref(v___x_313_);
v___x_315_ = lean_array_push(v___x_311_, v___x_314_);
v___x_316_ = lean_array_push(v___x_315_, v_a_303_);
v___x_317_ = l_Lean_Fmt_Layouts_atomic(v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = l_Lean_Fmt_TaggedDoc_nested(v___x_317_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_318_);
v___x_320_ = v___x_306_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_a_304_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_dec(v_a_298_);
lean_dec(v_a_293_);
lean_dec(v_a_288_);
lean_dec(v_a_283_);
return v___x_302_;
}
}
else
{
lean_dec(v_a_293_);
lean_dec(v_a_288_);
lean_dec(v_a_283_);
lean_dec(v_x_273_);
return v___x_297_;
}
}
else
{
lean_dec(v_a_288_);
lean_dec(v_a_283_);
lean_dec(v_x_273_);
return v___x_292_;
}
}
else
{
lean_dec(v_a_283_);
lean_dec(v_x_273_);
return v___x_287_;
}
}
else
{
lean_dec(v_x_273_);
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGetElemProof___boxed(lean_object* v_x_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Fmt_fmtGetElemProof(v_x_323_, v_a_324_, v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1(){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_333_ = l_Lean_Fmt_fmtAttribute;
v___x_334_ = ((lean_object*)(l_Lean_Fmt_fmtGetElemProof___closed__1));
v___x_335_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___closed__1));
v___x_336_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGetElemProof___boxed), 3, 0);
v___x_337_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_333_, v___x_334_, v___x_335_, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1___boxed(lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1();
return v_res_339_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_GetElem(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElem___regBuiltin_Lean_Fmt_fmtGetElem__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemQuestion___regBuiltin_Lean_Fmt_fmtGetElemQuestion__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemExclamation___regBuiltin_Lean_Fmt_fmtGetElemExclamation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_GetElem_0__Lean_Fmt_fmtGetElemProof___regBuiltin_Lean_Fmt_fmtGetElemProof__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_GetElem(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_GetElem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_GetElem(builtin);
}
#ifdef __cplusplus
}
#endif
