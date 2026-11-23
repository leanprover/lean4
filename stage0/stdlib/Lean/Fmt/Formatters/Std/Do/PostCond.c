// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Do.PostCond
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Do.PostCond import Init.Data
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object*);
lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPostCond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtPostCond___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPostCond___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtPostCond___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Fmt_fmtPostCond___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPostCond___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtPostCond___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "termPost⟨_,,⟩"};
static const lean_object* l_Lean_Fmt_fmtPostCond___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtPostCond___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtPostCond___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtPostCond___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtPostCond___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 45, 176, 130, 225, 239, 187, 245)}};
static const lean_object* l_Lean_Fmt_fmtPostCond___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtPostCond___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostCond(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostCond___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtPostCond"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 183, 113, 237, 75, 193, 219, 64)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtNoThrowPostCond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 10, .m_data = "term_⇓_=>_"};
static const lean_object* l_Lean_Fmt_fmtNoThrowPostCond___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtNoThrowPostCond___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtNoThrowPostCond___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtNoThrowPostCond___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNoThrowPostCond___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtNoThrowPostCond___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNoThrowPostCond___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNoThrowPostCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 118, 219, 9, 44, 173, 117, 117)}};
static const lean_object* l_Lean_Fmt_fmtNoThrowPostCond___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtNoThrowPostCond___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtNoThrowPostCond___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Fmt_fmtNoThrowPostCond___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtNoThrowPostCond___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtNoThrowPostCond___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNoThrowPostCond___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Fmt_fmtNoThrowPostCond___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtNoThrowPostCond___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNoThrowPostCond(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNoThrowPostCond___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtNoThrowPostCond"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 148, 167, 150, 86, 133, 141, 30)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMayThrowPostCond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "term_⇓\?_=>_"};
static const lean_object* l_Lean_Fmt_fmtMayThrowPostCond___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMayThrowPostCond___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMayThrowPostCond___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtMayThrowPostCond___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMayThrowPostCond___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPostCond___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtMayThrowPostCond___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMayThrowPostCond___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMayThrowPostCond___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 52, 46, 60, 233, 87, 205, 70)}};
static const lean_object* l_Lean_Fmt_fmtMayThrowPostCond___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMayThrowPostCond___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMayThrowPostCond(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMayThrowPostCond___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtMayThrowPostCond"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 78, 43, 145, 230, 67, 223, 19)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostCond(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_Fmt_fmtPostCond___closed__3));
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
lean_object* v___x_15_; lean_object* v_lbTk_16_; lean_object* v___x_17_; 
v___x_15_ = lean_unsigned_to_nat(0u);
v_lbTk_16_ = l_Lean_Syntax_getArg(v_x_8_, v___x_15_);
v___x_17_ = l_Lean_Fmt_fmt(v_lbTk_16_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v_handlers_22_; lean_object* v___x_23_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_17_, 2);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_8_, v___x_20_);
v_handlers_22_ = l_Lean_Syntax_getArgs(v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = l_Lean_Fmt_fmtTSepArray___redArg(v_handlers_22_, v_a_9_, v_a_19_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v_a_25_; lean_object* v___x_26_; lean_object* v_rbTk_27_; lean_object* v___x_28_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
v_a_25_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_a_25_);
lean_dec_ref_known(v___x_23_, 2);
v___x_26_ = lean_unsigned_to_nat(2u);
v_rbTk_27_ = l_Lean_Syntax_getArg(v_x_8_, v___x_26_);
lean_dec(v_x_8_);
v___x_28_ = l_Lean_Fmt_fmt(v_rbTk_27_, v_a_9_, v_a_25_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_39_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_39_ == 0)
{
v___x_32_ = v___x_28_;
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_34_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_a_24_);
v___x_35_ = l_Lean_Fmt_Layouts_metaApplication(v_a_18_, v___x_34_, v_a_29_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_35_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_a_30_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_dec(v_a_24_);
lean_dec(v_a_18_);
return v___x_28_;
}
}
else
{
lean_object* v_a_40_; lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_a_18_);
lean_dec(v_x_8_);
v_a_40_ = lean_ctor_get(v___x_23_, 0);
v_a_41_ = lean_ctor_get(v___x_23_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_23_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_inc(v_a_40_);
lean_dec(v___x_23_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_40_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostCond___boxed(lean_object* v_x_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Fmt_fmtPostCond(v_x_49_, v_a_50_, v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = l_Lean_Fmt_fmtAttribute;
v___x_62_ = ((lean_object*)(l_Lean_Fmt_fmtPostCond___closed__3));
v___x_63_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___closed__3));
v___x_64_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostCond___boxed), 3, 0);
v___x_65_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_61_, v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNoThrowPostCond(lean_object* v_x_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Fmt_fmtNoThrowPostCond___closed__1));
lean_inc(v_x_76_);
v___x_80_ = l_Lean_Syntax_isOfKind(v_x_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_x_76_);
v___x_81_ = l_Lean_Fmt_Error_partialFormatter;
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_78_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_Syntax_getArg(v_x_76_, v___x_83_);
v___x_85_ = ((lean_object*)(l_Lean_Fmt_fmtNoThrowPostCond___closed__3));
v___x_86_ = l_Lean_Syntax_isOfKind(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_x_76_);
v___x_87_ = l_Lean_Fmt_Error_partialFormatter;
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_a_78_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v_noThrowTk_90_; lean_object* v___x_91_; 
v___x_89_ = lean_unsigned_to_nat(1u);
v_noThrowTk_90_ = l_Lean_Syntax_getArg(v_x_76_, v___x_89_);
v___x_91_ = l_Lean_Fmt_fmt(v_noThrowTk_90_, v_a_77_, v_a_78_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_xs_96_; lean_object* v___x_97_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v___x_91_, 1);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_91_, 2);
v___x_94_ = lean_unsigned_to_nat(2u);
v___x_95_ = l_Lean_Syntax_getArg(v_x_76_, v___x_94_);
v_xs_96_ = l_Lean_Syntax_getArgs(v___x_95_);
lean_dec(v___x_95_);
v___x_97_ = l_Lean_Fmt_fmtArray___redArg(v_xs_96_, v_a_77_, v_a_93_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v_a_99_; lean_object* v___x_100_; lean_object* v_arrowTk_101_; lean_object* v___x_102_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
v_a_99_ = lean_ctor_get(v___x_97_, 1);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_97_, 2);
v___x_100_ = lean_unsigned_to_nat(3u);
v_arrowTk_101_ = l_Lean_Syntax_getArg(v_x_76_, v___x_100_);
v___x_102_ = l_Lean_Fmt_fmt(v_arrowTk_101_, v_a_77_, v_a_99_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
v_a_104_ = lean_ctor_get(v___x_102_, 1);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_102_, 2);
v___x_105_ = lean_unsigned_to_nat(4u);
v___x_106_ = l_Lean_Syntax_getArg(v_x_76_, v___x_105_);
lean_dec(v_x_76_);
v___x_107_ = l_Lean_Fmt_fmt(v___x_106_, v_a_77_, v_a_104_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_120_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_a_109_ = lean_ctor_get(v___x_107_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_120_ == 0)
{
v___x_111_ = v___x_107_;
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_113_ = l_Lean_Fmt_Layouts_fill(v_a_98_);
lean_dec(v_a_98_);
v___x_114_ = 2;
v___x_115_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_92_, v___x_113_, v___x_114_);
v___x_116_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_115_, v_a_103_, v_a_108_, v___x_86_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_116_);
v___x_118_ = v___x_111_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_a_109_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_dec(v_a_103_);
lean_dec(v_a_98_);
lean_dec(v_a_92_);
return v___x_107_;
}
}
else
{
lean_dec(v_a_98_);
lean_dec(v_a_92_);
lean_dec(v_x_76_);
return v___x_102_;
}
}
else
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec(v_a_92_);
lean_dec(v_x_76_);
v_a_121_ = lean_ctor_get(v___x_97_, 0);
v_a_122_ = lean_ctor_get(v___x_97_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_97_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_inc(v_a_121_);
lean_dec(v___x_97_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_121_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_dec(v_x_76_);
return v___x_91_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNoThrowPostCond___boxed(lean_object* v_x_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Fmt_fmtNoThrowPostCond(v_x_130_, v_a_131_, v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1(){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_140_ = l_Lean_Fmt_fmtAttribute;
v___x_141_ = ((lean_object*)(l_Lean_Fmt_fmtNoThrowPostCond___closed__1));
v___x_142_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___closed__1));
v___x_143_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtNoThrowPostCond___boxed), 3, 0);
v___x_144_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_140_, v___x_141_, v___x_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1___boxed(lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMayThrowPostCond(lean_object* v_x_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Fmt_fmtMayThrowPostCond___closed__1));
lean_inc(v_x_152_);
v___x_156_ = l_Lean_Syntax_isOfKind(v_x_152_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_x_152_);
v___x_157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v_a_154_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = l_Lean_Syntax_getArg(v_x_152_, v___x_159_);
v___x_161_ = ((lean_object*)(l_Lean_Fmt_fmtNoThrowPostCond___closed__3));
v___x_162_ = l_Lean_Syntax_isOfKind(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_x_152_);
v___x_163_ = l_Lean_Fmt_Error_partialFormatter;
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_a_154_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v_mayThrowTk_166_; lean_object* v___x_167_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v_mayThrowTk_166_ = l_Lean_Syntax_getArg(v_x_152_, v___x_165_);
v___x_167_ = l_Lean_Fmt_fmt(v_mayThrowTk_166_, v_a_153_, v_a_154_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_xs_172_; lean_object* v___x_173_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
v_a_169_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_167_, 2);
v___x_170_ = lean_unsigned_to_nat(2u);
v___x_171_ = l_Lean_Syntax_getArg(v_x_152_, v___x_170_);
v_xs_172_ = l_Lean_Syntax_getArgs(v___x_171_);
lean_dec(v___x_171_);
v___x_173_ = l_Lean_Fmt_fmtArray___redArg(v_xs_172_, v_a_153_, v_a_169_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v_arrowTk_177_; lean_object* v___x_178_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
v_a_175_ = lean_ctor_get(v___x_173_, 1);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_173_, 2);
v___x_176_ = lean_unsigned_to_nat(3u);
v_arrowTk_177_ = l_Lean_Syntax_getArg(v_x_152_, v___x_176_);
v___x_178_ = l_Lean_Fmt_fmt(v_arrowTk_177_, v_a_153_, v_a_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
v_a_180_ = lean_ctor_get(v___x_178_, 1);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_178_, 2);
v___x_181_ = lean_unsigned_to_nat(4u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_152_, v___x_181_);
lean_dec(v_x_152_);
v___x_183_ = l_Lean_Fmt_fmt(v___x_182_, v_a_153_, v_a_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_196_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_a_185_ = lean_ctor_get(v___x_183_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_196_ == 0)
{
v___x_187_ = v___x_183_;
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_189_ = l_Lean_Fmt_Layouts_fill(v_a_174_);
lean_dec(v_a_174_);
v___x_190_ = 2;
v___x_191_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_168_, v___x_189_, v___x_190_);
v___x_192_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_191_, v_a_179_, v_a_184_, v___x_162_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_192_);
v___x_194_ = v___x_187_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_a_185_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
else
{
lean_dec(v_a_179_);
lean_dec(v_a_174_);
lean_dec(v_a_168_);
return v___x_183_;
}
}
else
{
lean_dec(v_a_174_);
lean_dec(v_a_168_);
lean_dec(v_x_152_);
return v___x_178_;
}
}
else
{
lean_object* v_a_197_; lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v_a_168_);
lean_dec(v_x_152_);
v_a_197_ = lean_ctor_get(v___x_173_, 0);
v_a_198_ = lean_ctor_get(v___x_173_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_173_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_inc(v_a_197_);
lean_dec(v___x_173_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_197_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_dec(v_x_152_);
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMayThrowPostCond___boxed(lean_object* v_x_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Fmt_fmtMayThrowPostCond(v_x_206_, v_a_207_, v_a_208_);
lean_dec_ref(v_a_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1(){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_216_ = l_Lean_Fmt_fmtAttribute;
v___x_217_ = ((lean_object*)(l_Lean_Fmt_fmtMayThrowPostCond___closed__1));
v___x_218_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___closed__1));
v___x_219_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMayThrowPostCond___boxed), 3, 0);
v___x_220_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_216_, v___x_217_, v___x_218_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1___boxed(lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1();
return v_res_222_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_PostCond(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtPostCond___regBuiltin_Lean_Fmt_fmtPostCond__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtNoThrowPostCond___regBuiltin_Lean_Fmt_fmtNoThrowPostCond__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Do_PostCond_0__Lean_Fmt_fmtMayThrowPostCond___regBuiltin_Lean_Fmt_fmtMayThrowPostCond__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Do_PostCond(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Do_PostCond(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Do_PostCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Do_PostCond(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Do_PostCond(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_PostCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_PostCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Do_PostCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Do_PostCond(builtin);
}
#ifdef __cplusplus
}
#endif
