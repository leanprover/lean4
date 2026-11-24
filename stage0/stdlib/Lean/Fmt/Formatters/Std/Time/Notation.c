// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Time.Notation
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Std.Time.Notation.Spec meta import Std.Time.Notation import Init.Data
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtZonedDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtZonedDateTime___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtZonedDateTime___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Time"};
static const lean_object* l_Lean_Fmt_fmtZonedDateTime___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtZonedDateTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termZoned(_)"};
static const lean_object* l_Lean_Fmt_fmtZonedDateTime___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtZonedDateTime___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtZonedDateTime___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtZonedDateTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 93, 126, 244, 143, 80, 158, 136)}};
static const lean_object* l_Lean_Fmt_fmtZonedDateTime___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtZonedDateTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtZonedDateTime___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtZonedDateTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtZonedDateTime___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtZonedDateTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtZonedDateTime___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtZonedDateTime"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(42, 114, 78, 158, 152, 252, 255, 190)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termZoned(_,_)"};
static const lean_object* l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 198, 165, 221, 166, 80, 106, 244)}};
static const lean_object* l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtZonedDateTimeWithTimeZone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "fmtZonedDateTimeWithTimeZone"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 179, 68, 19, 173, 97, 124, 242)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPlainDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "termDatetime(_)"};
static const lean_object* l_Lean_Fmt_fmtPlainDateTime___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPlainDateTime___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtPlainDateTime___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtPlainDateTime___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPlainDateTime___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtPlainDateTime___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPlainDateTime___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtPlainDateTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 97, 38, 153, 227, 76, 238, 149)}};
static const lean_object* l_Lean_Fmt_fmtPlainDateTime___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPlainDateTime___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainDateTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainDateTime___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtPlainDateTime"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 116, 205, 174, 145, 193, 95, 20)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPlainDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "termDate(_)"};
static const lean_object* l_Lean_Fmt_fmtPlainDate___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPlainDate___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtPlainDate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtPlainDate___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPlainDate___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtPlainDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPlainDate___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtPlainDate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 19, 6, 45, 102, 199, 247, 82)}};
static const lean_object* l_Lean_Fmt_fmtPlainDate___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPlainDate___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainDate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainDate___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtPlainDate"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 9, 81, 180, 54, 37, 206, 72)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPlainTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "termTime(_)"};
static const lean_object* l_Lean_Fmt_fmtPlainTime___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPlainTime___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtPlainTime___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtPlainTime___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPlainTime___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtPlainTime___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPlainTime___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtPlainTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 133, 123, 15, 138, 216, 108, 236)}};
static const lean_object* l_Lean_Fmt_fmtPlainTime___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPlainTime___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainTime___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtPlainTime"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 121, 122, 82, 91, 44, 242, 148)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTimeZoneOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "termOffset(_)"};
static const lean_object* l_Lean_Fmt_fmtTimeZoneOffset___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTimeZoneOffset___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTimeZoneOffset___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtTimeZoneOffset___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTimeZoneOffset___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtTimeZoneOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTimeZoneOffset___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTimeZoneOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 188, 135, 138, 129, 64, 205, 196)}};
static const lean_object* l_Lean_Fmt_fmtTimeZoneOffset___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTimeZoneOffset___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeZoneOffset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeZoneOffset___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtTimeZoneOffset"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 244, 210, 207, 245, 238, 117, 107)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTimeZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "termTimezone(_)"};
static const lean_object* l_Lean_Fmt_fmtTimeZone___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTimeZone___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTimeZone___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtTimeZone___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTimeZone___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtZonedDateTime___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtTimeZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTimeZone___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTimeZone___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 93, 67, 49, 253, 69, 174, 185)}};
static const lean_object* l_Lean_Fmt_fmtTimeZone___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTimeZone___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeZone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeZone___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtTimeZone"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 175, 228, 103, 10, 78, 196, 193)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtZonedDateTime(lean_object* v_x_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__3));
lean_inc(v_x_11_);
v___x_15_ = l_Lean_Syntax_isOfKind(v_x_11_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_x_11_);
v___x_16_ = l_Lean_Fmt_Error_partialFormatter;
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_a_13_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = l_Lean_Syntax_getArg(v_x_11_, v___x_18_);
v___x_20_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__5));
lean_inc(v___x_19_);
v___x_21_ = l_Lean_Syntax_isOfKind(v___x_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v___x_19_);
lean_dec(v_x_11_);
v___x_22_ = l_Lean_Fmt_Error_partialFormatter;
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v_a_13_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v_lbTk_25_; lean_object* v___x_26_; 
v___x_24_ = lean_unsigned_to_nat(0u);
v_lbTk_25_ = l_Lean_Syntax_getArg(v_x_11_, v___x_24_);
v___x_26_ = l_Lean_Fmt_fmt(v_lbTk_25_, v_a_12_, v_a_13_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_a_27_);
v_a_28_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_a_28_);
lean_dec_ref_known(v___x_26_, 2);
v___x_29_ = l_Lean_Fmt_fmt(v___x_19_, v_a_12_, v_a_28_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_32_; lean_object* v_rbTk_33_; lean_object* v___x_34_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_a_30_);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
lean_inc(v_a_31_);
lean_dec_ref_known(v___x_29_, 2);
v___x_32_ = lean_unsigned_to_nat(2u);
v_rbTk_33_ = l_Lean_Syntax_getArg(v_x_11_, v___x_32_);
lean_dec(v_x_11_);
v___x_34_ = l_Lean_Fmt_fmt(v_rbTk_33_, v_a_12_, v_a_31_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_48_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_a_36_ = lean_ctor_get(v___x_34_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_48_ == 0)
{
v___x_38_ = v___x_34_;
v_isShared_39_ = v_isSharedCheck_48_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_48_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_40_ = lean_mk_empty_array_with_capacity(v___x_18_);
lean_inc_ref(v___x_40_);
v___x_41_ = lean_array_push(v___x_40_, v_a_30_);
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
v___x_43_ = lean_array_push(v___x_40_, v___x_42_);
v___x_44_ = l_Lean_Fmt_Layouts_metaApplication(v_a_27_, v___x_43_, v_a_35_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v___x_44_);
v___x_46_ = v___x_38_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_a_36_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
else
{
lean_dec(v_a_30_);
lean_dec(v_a_27_);
return v___x_34_;
}
}
else
{
lean_dec(v_a_27_);
lean_dec(v_x_11_);
return v___x_29_;
}
}
else
{
lean_dec(v___x_19_);
lean_dec(v_x_11_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtZonedDateTime___boxed(lean_object* v_x_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Fmt_fmtZonedDateTime(v_x_49_, v_a_50_, v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = l_Lean_Fmt_fmtAttribute;
v___x_62_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__3));
v___x_63_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___closed__3));
v___x_64_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtZonedDateTime___boxed), 3, 0);
v___x_65_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_61_, v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtZonedDateTimeWithTimeZone(lean_object* v_x_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1));
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
v___x_82_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__5));
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
lean_object* v___x_86_; lean_object* v_lbTk_87_; lean_object* v___x_88_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v_lbTk_87_ = l_Lean_Syntax_getArg(v_x_73_, v___x_86_);
v___x_88_ = l_Lean_Fmt_fmt(v_lbTk_87_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v___x_91_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
v_a_90_ = lean_ctor_get(v___x_88_, 1);
lean_inc(v_a_90_);
lean_dec_ref_known(v___x_88_, 2);
v___x_91_ = l_Lean_Fmt_fmt(v___x_81_, v_a_74_, v_a_90_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_94_; lean_object* v_commaTk_95_; lean_object* v___x_96_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v___x_91_, 1);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_91_, 2);
v___x_94_ = lean_unsigned_to_nat(2u);
v_commaTk_95_ = l_Lean_Syntax_getArg(v_x_73_, v___x_94_);
v___x_96_ = l_Lean_Fmt_fmt(v_commaTk_95_, v_a_74_, v_a_93_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_96_, 2);
v___x_99_ = lean_unsigned_to_nat(3u);
v___x_100_ = l_Lean_Syntax_getArg(v_x_73_, v___x_99_);
v___x_101_ = l_Lean_Fmt_fmt(v___x_100_, v_a_74_, v_a_98_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v_rbTk_105_; lean_object* v___x_106_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
v_a_103_ = lean_ctor_get(v___x_101_, 1);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_101_, 2);
v___x_104_ = lean_unsigned_to_nat(4u);
v_rbTk_105_ = l_Lean_Syntax_getArg(v_x_73_, v___x_104_);
lean_dec(v_x_73_);
v___x_106_ = l_Lean_Fmt_fmt(v_rbTk_105_, v_a_74_, v_a_103_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_126_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_a_108_ = lean_ctor_get(v___x_106_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_126_ == 0)
{
v___x_110_ = v___x_106_;
v_isShared_111_ = v_isSharedCheck_126_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_126_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_112_ = lean_mk_empty_array_with_capacity(v___x_80_);
lean_inc_ref(v___x_112_);
v___x_113_ = lean_array_push(v___x_112_, v_a_92_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v_a_97_);
v___x_116_ = lean_array_push(v___x_112_, v_a_102_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
v___x_118_ = lean_mk_empty_array_with_capacity(v___x_99_);
v___x_119_ = lean_array_push(v___x_118_, v___x_114_);
v___x_120_ = lean_array_push(v___x_119_, v___x_115_);
v___x_121_ = lean_array_push(v___x_120_, v___x_117_);
v___x_122_ = l_Lean_Fmt_Layouts_metaApplication(v_a_89_, v___x_121_, v_a_107_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_122_);
v___x_124_ = v___x_110_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_a_108_);
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
lean_dec(v_a_102_);
lean_dec(v_a_97_);
lean_dec(v_a_92_);
lean_dec(v_a_89_);
return v___x_106_;
}
}
else
{
lean_dec(v_a_97_);
lean_dec(v_a_92_);
lean_dec(v_a_89_);
lean_dec(v_x_73_);
return v___x_101_;
}
}
else
{
lean_dec(v_a_92_);
lean_dec(v_a_89_);
lean_dec(v_x_73_);
return v___x_96_;
}
}
else
{
lean_dec(v_a_89_);
lean_dec(v_x_73_);
return v___x_91_;
}
}
else
{
lean_dec(v___x_81_);
lean_dec(v_x_73_);
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___boxed(lean_object* v_x_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Fmt_fmtZonedDateTimeWithTimeZone(v_x_127_, v_a_128_, v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1(){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_137_ = l_Lean_Fmt_fmtAttribute;
v___x_138_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___closed__1));
v___x_139_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___closed__1));
v___x_140_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtZonedDateTimeWithTimeZone___boxed), 3, 0);
v___x_141_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_137_, v___x_138_, v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1___boxed(lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1();
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainDateTime(lean_object* v_x_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Fmt_fmtPlainDateTime___closed__1));
lean_inc(v_x_149_);
v___x_153_ = l_Lean_Syntax_isOfKind(v_x_149_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_x_149_);
v___x_154_ = l_Lean_Fmt_Error_partialFormatter;
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_151_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = l_Lean_Syntax_getArg(v_x_149_, v___x_156_);
v___x_158_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__5));
lean_inc(v___x_157_);
v___x_159_ = l_Lean_Syntax_isOfKind(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v___x_157_);
lean_dec(v_x_149_);
v___x_160_ = l_Lean_Fmt_Error_partialFormatter;
v___x_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_a_151_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v_lbTk_163_; lean_object* v___x_164_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v_lbTk_163_ = l_Lean_Syntax_getArg(v_x_149_, v___x_162_);
v___x_164_ = l_Lean_Fmt_fmt(v_lbTk_163_, v_a_150_, v_a_151_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v_a_166_; lean_object* v___x_167_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
v_a_166_ = lean_ctor_get(v___x_164_, 1);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_164_, 2);
v___x_167_ = l_Lean_Fmt_fmt(v___x_157_, v_a_150_, v_a_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_170_; lean_object* v_rbTk_171_; lean_object* v___x_172_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
v_a_169_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_167_, 2);
v___x_170_ = lean_unsigned_to_nat(2u);
v_rbTk_171_ = l_Lean_Syntax_getArg(v_x_149_, v___x_170_);
lean_dec(v_x_149_);
v___x_172_ = l_Lean_Fmt_fmt(v_rbTk_171_, v_a_150_, v_a_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_186_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_a_174_ = lean_ctor_get(v___x_172_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_186_ == 0)
{
v___x_176_ = v___x_172_;
v_isShared_177_ = v_isSharedCheck_186_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_186_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_178_ = lean_mk_empty_array_with_capacity(v___x_156_);
lean_inc_ref(v___x_178_);
v___x_179_ = lean_array_push(v___x_178_, v_a_168_);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
v___x_181_ = lean_array_push(v___x_178_, v___x_180_);
v___x_182_ = l_Lean_Fmt_Layouts_metaApplication(v_a_165_, v___x_181_, v_a_173_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_182_);
v___x_184_ = v___x_176_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_a_174_);
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
lean_dec(v_a_168_);
lean_dec(v_a_165_);
return v___x_172_;
}
}
else
{
lean_dec(v_a_165_);
lean_dec(v_x_149_);
return v___x_167_;
}
}
else
{
lean_dec(v___x_157_);
lean_dec(v_x_149_);
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainDateTime___boxed(lean_object* v_x_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Fmt_fmtPlainDateTime(v_x_187_, v_a_188_, v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1(){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = l_Lean_Fmt_fmtAttribute;
v___x_198_ = ((lean_object*)(l_Lean_Fmt_fmtPlainDateTime___closed__1));
v___x_199_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___closed__1));
v___x_200_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPlainDateTime___boxed), 3, 0);
v___x_201_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_197_, v___x_198_, v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1___boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1();
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainDate(lean_object* v_x_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Fmt_fmtPlainDate___closed__1));
lean_inc(v_x_209_);
v___x_213_ = l_Lean_Syntax_isOfKind(v_x_209_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_x_209_);
v___x_214_ = l_Lean_Fmt_Error_partialFormatter;
v___x_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_a_211_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = l_Lean_Syntax_getArg(v_x_209_, v___x_216_);
v___x_218_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__5));
lean_inc(v___x_217_);
v___x_219_ = l_Lean_Syntax_isOfKind(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v___x_217_);
lean_dec(v_x_209_);
v___x_220_ = l_Lean_Fmt_Error_partialFormatter;
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_211_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v_lbTk_223_; lean_object* v___x_224_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v_lbTk_223_ = l_Lean_Syntax_getArg(v_x_209_, v___x_222_);
v___x_224_ = l_Lean_Fmt_fmt(v_lbTk_223_, v_a_210_, v_a_211_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v_a_226_; lean_object* v___x_227_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
v_a_226_ = lean_ctor_get(v___x_224_, 1);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_224_, 2);
v___x_227_ = l_Lean_Fmt_fmt(v___x_217_, v_a_210_, v_a_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v_a_229_; lean_object* v___x_230_; lean_object* v_rbTk_231_; lean_object* v___x_232_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
v_a_229_ = lean_ctor_get(v___x_227_, 1);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_227_, 2);
v___x_230_ = lean_unsigned_to_nat(2u);
v_rbTk_231_ = l_Lean_Syntax_getArg(v_x_209_, v___x_230_);
lean_dec(v_x_209_);
v___x_232_ = l_Lean_Fmt_fmt(v_rbTk_231_, v_a_210_, v_a_229_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_246_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_a_234_ = lean_ctor_get(v___x_232_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_246_ == 0)
{
v___x_236_ = v___x_232_;
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_238_ = lean_mk_empty_array_with_capacity(v___x_216_);
lean_inc_ref(v___x_238_);
v___x_239_ = lean_array_push(v___x_238_, v_a_228_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
v___x_241_ = lean_array_push(v___x_238_, v___x_240_);
v___x_242_ = l_Lean_Fmt_Layouts_metaApplication(v_a_225_, v___x_241_, v_a_233_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_242_);
v___x_244_ = v___x_236_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_a_234_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_dec(v_a_228_);
lean_dec(v_a_225_);
return v___x_232_;
}
}
else
{
lean_dec(v_a_225_);
lean_dec(v_x_209_);
return v___x_227_;
}
}
else
{
lean_dec(v___x_217_);
lean_dec(v_x_209_);
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainDate___boxed(lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Fmt_fmtPlainDate(v_x_247_, v_a_248_, v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1(){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_257_ = l_Lean_Fmt_fmtAttribute;
v___x_258_ = ((lean_object*)(l_Lean_Fmt_fmtPlainDate___closed__1));
v___x_259_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___closed__1));
v___x_260_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPlainDate___boxed), 3, 0);
v___x_261_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_257_, v___x_258_, v___x_259_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1___boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1();
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainTime(lean_object* v_x_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Fmt_fmtPlainTime___closed__1));
lean_inc(v_x_269_);
v___x_273_ = l_Lean_Syntax_isOfKind(v_x_269_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v_x_269_);
v___x_274_ = l_Lean_Fmt_Error_partialFormatter;
v___x_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v_a_271_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = l_Lean_Syntax_getArg(v_x_269_, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__5));
lean_inc(v___x_277_);
v___x_279_ = l_Lean_Syntax_isOfKind(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v___x_277_);
lean_dec(v_x_269_);
v___x_280_ = l_Lean_Fmt_Error_partialFormatter;
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_a_271_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v_lbTk_283_; lean_object* v___x_284_; 
v___x_282_ = lean_unsigned_to_nat(0u);
v_lbTk_283_ = l_Lean_Syntax_getArg(v_x_269_, v___x_282_);
v___x_284_ = l_Lean_Fmt_fmt(v_lbTk_283_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v_a_286_; lean_object* v___x_287_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
v_a_286_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_284_, 2);
v___x_287_ = l_Lean_Fmt_fmt(v___x_277_, v_a_270_, v_a_286_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v_a_289_; lean_object* v___x_290_; lean_object* v_rbTk_291_; lean_object* v___x_292_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
v_a_289_ = lean_ctor_get(v___x_287_, 1);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_287_, 2);
v___x_290_ = lean_unsigned_to_nat(2u);
v_rbTk_291_ = l_Lean_Syntax_getArg(v_x_269_, v___x_290_);
lean_dec(v_x_269_);
v___x_292_ = l_Lean_Fmt_fmt(v_rbTk_291_, v_a_270_, v_a_289_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_306_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_a_294_ = lean_ctor_get(v___x_292_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_306_ == 0)
{
v___x_296_ = v___x_292_;
v_isShared_297_ = v_isSharedCheck_306_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_306_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_298_ = lean_mk_empty_array_with_capacity(v___x_276_);
lean_inc_ref(v___x_298_);
v___x_299_ = lean_array_push(v___x_298_, v_a_288_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___x_301_ = lean_array_push(v___x_298_, v___x_300_);
v___x_302_ = l_Lean_Fmt_Layouts_metaApplication(v_a_285_, v___x_301_, v_a_293_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_302_);
v___x_304_ = v___x_296_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_a_294_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_dec(v_a_288_);
lean_dec(v_a_285_);
return v___x_292_;
}
}
else
{
lean_dec(v_a_285_);
lean_dec(v_x_269_);
return v___x_287_;
}
}
else
{
lean_dec(v___x_277_);
lean_dec(v_x_269_);
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPlainTime___boxed(lean_object* v_x_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Fmt_fmtPlainTime(v_x_307_, v_a_308_, v_a_309_);
lean_dec_ref(v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1(){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = l_Lean_Fmt_fmtAttribute;
v___x_318_ = ((lean_object*)(l_Lean_Fmt_fmtPlainTime___closed__1));
v___x_319_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___closed__1));
v___x_320_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPlainTime___boxed), 3, 0);
v___x_321_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_317_, v___x_318_, v___x_319_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1___boxed(lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1();
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeZoneOffset(lean_object* v_x_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Fmt_fmtTimeZoneOffset___closed__1));
lean_inc(v_x_329_);
v___x_333_ = l_Lean_Syntax_isOfKind(v_x_329_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec(v_x_329_);
v___x_334_ = l_Lean_Fmt_Error_partialFormatter;
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_331_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = l_Lean_Syntax_getArg(v_x_329_, v___x_336_);
v___x_338_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__5));
lean_inc(v___x_337_);
v___x_339_ = l_Lean_Syntax_isOfKind(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v___x_337_);
lean_dec(v_x_329_);
v___x_340_ = l_Lean_Fmt_Error_partialFormatter;
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v_a_331_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v_lbTk_343_; lean_object* v___x_344_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v_lbTk_343_ = l_Lean_Syntax_getArg(v_x_329_, v___x_342_);
v___x_344_ = l_Lean_Fmt_fmt(v_lbTk_343_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v_a_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
v_a_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_344_, 2);
v___x_347_ = l_Lean_Fmt_fmt(v___x_337_, v_a_330_, v_a_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v_rbTk_351_; lean_object* v___x_352_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
v_a_349_ = lean_ctor_get(v___x_347_, 1);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_347_, 2);
v___x_350_ = lean_unsigned_to_nat(2u);
v_rbTk_351_ = l_Lean_Syntax_getArg(v_x_329_, v___x_350_);
lean_dec(v_x_329_);
v___x_352_ = l_Lean_Fmt_fmt(v_rbTk_351_, v_a_330_, v_a_349_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_366_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_a_354_ = lean_ctor_get(v___x_352_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_366_ == 0)
{
v___x_356_ = v___x_352_;
v_isShared_357_ = v_isSharedCheck_366_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_366_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_358_ = lean_mk_empty_array_with_capacity(v___x_336_);
lean_inc_ref(v___x_358_);
v___x_359_ = lean_array_push(v___x_358_, v_a_348_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
v___x_361_ = lean_array_push(v___x_358_, v___x_360_);
v___x_362_ = l_Lean_Fmt_Layouts_metaApplication(v_a_345_, v___x_361_, v_a_353_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_362_);
v___x_364_ = v___x_356_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_a_354_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_dec(v_a_348_);
lean_dec(v_a_345_);
return v___x_352_;
}
}
else
{
lean_dec(v_a_345_);
lean_dec(v_x_329_);
return v___x_347_;
}
}
else
{
lean_dec(v___x_337_);
lean_dec(v_x_329_);
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeZoneOffset___boxed(lean_object* v_x_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Fmt_fmtTimeZoneOffset(v_x_367_, v_a_368_, v_a_369_);
lean_dec_ref(v_a_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1(){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_377_ = l_Lean_Fmt_fmtAttribute;
v___x_378_ = ((lean_object*)(l_Lean_Fmt_fmtTimeZoneOffset___closed__1));
v___x_379_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___closed__1));
v___x_380_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTimeZoneOffset___boxed), 3, 0);
v___x_381_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_377_, v___x_378_, v___x_379_, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1___boxed(lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1();
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeZone(lean_object* v_x_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_Fmt_fmtTimeZone___closed__1));
lean_inc(v_x_389_);
v___x_393_ = l_Lean_Syntax_isOfKind(v_x_389_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v_x_389_);
v___x_394_ = l_Lean_Fmt_Error_partialFormatter;
v___x_395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_a_391_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = l_Lean_Syntax_getArg(v_x_389_, v___x_396_);
v___x_398_ = ((lean_object*)(l_Lean_Fmt_fmtZonedDateTime___closed__5));
lean_inc(v___x_397_);
v___x_399_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v___x_397_);
lean_dec(v_x_389_);
v___x_400_ = l_Lean_Fmt_Error_partialFormatter;
v___x_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v_a_391_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v_lbTk_403_; lean_object* v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v_lbTk_403_ = l_Lean_Syntax_getArg(v_x_389_, v___x_402_);
v___x_404_ = l_Lean_Fmt_fmt(v_lbTk_403_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v_a_406_; lean_object* v___x_407_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
v_a_406_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_404_, 2);
v___x_407_ = l_Lean_Fmt_fmt(v___x_397_, v_a_390_, v_a_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v_a_409_; lean_object* v___x_410_; lean_object* v_rbTk_411_; lean_object* v___x_412_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
v_a_409_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_407_, 2);
v___x_410_ = lean_unsigned_to_nat(2u);
v_rbTk_411_ = l_Lean_Syntax_getArg(v_x_389_, v___x_410_);
lean_dec(v_x_389_);
v___x_412_ = l_Lean_Fmt_fmt(v_rbTk_411_, v_a_390_, v_a_409_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_426_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_a_414_ = lean_ctor_get(v___x_412_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_426_ == 0)
{
v___x_416_ = v___x_412_;
v_isShared_417_ = v_isSharedCheck_426_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_426_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_418_ = lean_mk_empty_array_with_capacity(v___x_396_);
lean_inc_ref(v___x_418_);
v___x_419_ = lean_array_push(v___x_418_, v_a_408_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
v___x_421_ = lean_array_push(v___x_418_, v___x_420_);
v___x_422_ = l_Lean_Fmt_Layouts_metaApplication(v_a_405_, v___x_421_, v_a_413_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_422_);
v___x_424_ = v___x_416_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_a_414_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_dec(v_a_408_);
lean_dec(v_a_405_);
return v___x_412_;
}
}
else
{
lean_dec(v_a_405_);
lean_dec(v_x_389_);
return v___x_407_;
}
}
else
{
lean_dec(v___x_397_);
lean_dec(v_x_389_);
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeZone___boxed(lean_object* v_x_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Fmt_fmtTimeZone(v_x_427_, v_a_428_, v_a_429_);
lean_dec_ref(v_a_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1(){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_437_ = l_Lean_Fmt_fmtAttribute;
v___x_438_ = ((lean_object*)(l_Lean_Fmt_fmtTimeZone___closed__1));
v___x_439_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___closed__1));
v___x_440_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTimeZone___boxed), 3, 0);
v___x_441_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_437_, v___x_438_, v___x_439_, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1___boxed(lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1();
return v_res_443_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Time_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTime___regBuiltin_Lean_Fmt_fmtZonedDateTime__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtZonedDateTimeWithTimeZone___regBuiltin_Lean_Fmt_fmtZonedDateTimeWithTimeZone__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDateTime___regBuiltin_Lean_Fmt_fmtPlainDateTime__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainDate___regBuiltin_Lean_Fmt_fmtPlainDate__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtPlainTime___regBuiltin_Lean_Fmt_fmtPlainTime__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZoneOffset___regBuiltin_Lean_Fmt_fmtTimeZoneOffset__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_0__Lean_Fmt_fmtTimeZone___regBuiltin_Lean_Fmt_fmtTimeZone__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Time_Notation(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Time_Notation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Time_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(uint8_t builtin);
lean_object* initialize_Std_Time_Notation(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Time_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Time_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Time_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Time_Notation(builtin);
}
#ifdef __cplusplus
}
#endif
