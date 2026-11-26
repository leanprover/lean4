// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Server.Test.Cancel
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Server.Test.Cancel import Init.Data
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Test"};
static const lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Cancel"};
static const lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "commandWait_for_cancel_once_command_"};
static const lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(226, 229, 56, 152, 161, 65, 10, 140)}};
static const lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "fmtWaitForCancelOnceCommand"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 226, 68, 208, 100, 207, 88, 82)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWaitForTestTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "tacticWait_for_test_task_"};
static const lean_object* l_Lean_Fmt_fmtWaitForTestTask___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtWaitForTestTask___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForTestTask___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForTestTask___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForTestTask___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForTestTask___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 241, 171, 98, 172, 75, 180, 122)}};
static const lean_object* l_Lean_Fmt_fmtWaitForTestTask___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtWaitForTestTask___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtWaitForTestTask___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtWaitForTestTask___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtWaitForTestTask___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtWaitForTestTask___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForTestTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForTestTask___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtWaitForTestTask"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 47, 116, 169, 122, 137, 145, 135)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWaitForSync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticWait_for_sync_"};
static const lean_object* l_Lean_Fmt_fmtWaitForSync___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWaitForSync___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtWaitForSync___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForSync___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForSync___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForSync___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForSync___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForSync___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForSync___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Fmt_fmtWaitForSync___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWaitForSync___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtWaitForSync___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 215, 46, 16, 187, 62, 147, 151)}};
static const lean_object* l_Lean_Fmt_fmtWaitForSync___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWaitForSync___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForSync(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForSync___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtWaitForSync"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 206, 52, 170, 62, 46, 88, 134)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBlockUntilCancelled___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "tacticBlock_until_cancelled_"};
static const lean_object* l_Lean_Fmt_fmtBlockUntilCancelled___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBlockUntilCancelled___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtBlockUntilCancelled___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 22, 208, 150, 242, 79, 233, 148)}};
static const lean_object* l_Lean_Fmt_fmtBlockUntilCancelled___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBlockUntilCancelled___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBlockUntilCancelled(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBlockUntilCancelled___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtBlockUntilCancelled"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 36, 177, 253, 84, 78, 182, 113)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand(lean_object* v_x_15_, lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5));
lean_inc(v_x_15_);
v___x_19_ = l_Lean_Syntax_isOfKind(v_x_15_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_x_15_);
v___x_20_ = l_Lean_Fmt_Error_partialFormatter;
v___x_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v_a_17_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = l_Lean_Syntax_getArg(v_x_15_, v___x_22_);
v___x_24_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__7));
lean_inc(v___x_23_);
v___x_25_ = l_Lean_Syntax_isOfKind(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v___x_23_);
lean_dec(v_x_15_);
v___x_26_ = l_Lean_Fmt_Error_partialFormatter;
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v_a_17_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v_waitTk_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v_waitTk_29_ = l_Lean_Syntax_getArg(v_x_15_, v___x_28_);
lean_dec(v_x_15_);
v___x_30_ = l_Lean_Fmt_fmt(v_waitTk_29_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v_a_32_; lean_object* v___x_33_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_31_);
v_a_32_ = lean_ctor_get(v___x_30_, 1);
lean_inc(v_a_32_);
lean_dec_ref_known(v___x_30_, 2);
v___x_33_ = l_Lean_Fmt_fmt(v___x_23_, v_a_16_, v_a_32_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_49_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_a_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_49_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_49_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_49_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_39_ = lean_unsigned_to_nat(2u);
v___x_40_ = lean_mk_empty_array_with_capacity(v___x_39_);
v___x_41_ = lean_array_push(v___x_40_, v_a_31_);
v___x_42_ = lean_array_push(v___x_41_, v_a_34_);
v___x_43_ = 0;
v___x_44_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_44_, 0, v___x_25_);
lean_ctor_set_uint8(v___x_44_, 1, v___x_43_);
lean_ctor_set_uint8(v___x_44_, 2, v___x_43_);
lean_ctor_set_uint8(v___x_44_, 3, v___x_43_);
v___x_45_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_42_, v___x_44_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_45_);
v___x_47_ = v___x_37_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_a_35_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
else
{
lean_dec(v_a_31_);
return v___x_33_;
}
}
else
{
lean_dec(v___x_23_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForCancelOnceCommand___boxed(lean_object* v_x_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Fmt_fmtWaitForCancelOnceCommand(v_x_50_, v_a_51_, v_a_52_);
lean_dec_ref(v_a_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = l_Lean_Fmt_fmtAttribute;
v___x_62_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForCancelOnceCommand___closed__5));
v___x_63_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___closed__2));
v___x_64_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtWaitForCancelOnceCommand___boxed), 3, 0);
v___x_65_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_61_, v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForTestTask(lean_object* v_x_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForTestTask___closed__1));
lean_inc(v_x_78_);
v___x_82_ = l_Lean_Syntax_isOfKind(v_x_78_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_x_78_);
v___x_83_ = l_Lean_Fmt_Error_partialFormatter;
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v_a_80_);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = l_Lean_Syntax_getArg(v_x_78_, v___x_85_);
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForTestTask___closed__3));
lean_inc(v___x_86_);
v___x_88_ = l_Lean_Syntax_isOfKind(v___x_86_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v___x_86_);
lean_dec(v_x_78_);
v___x_89_ = l_Lean_Fmt_Error_partialFormatter;
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_a_80_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_waitTk_92_; lean_object* v___x_93_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v_waitTk_92_ = l_Lean_Syntax_getArg(v_x_78_, v___x_91_);
lean_dec(v_x_78_);
v___x_93_ = l_Lean_Fmt_fmt(v_waitTk_92_, v_a_79_, v_a_80_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v___x_96_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
v_a_95_ = lean_ctor_get(v___x_93_, 1);
lean_inc(v_a_95_);
lean_dec_ref_known(v___x_93_, 2);
v___x_96_ = l_Lean_Fmt_fmt(v___x_86_, v_a_79_, v_a_95_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_112_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_112_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_112_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_112_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_102_ = lean_unsigned_to_nat(2u);
v___x_103_ = lean_mk_empty_array_with_capacity(v___x_102_);
v___x_104_ = lean_array_push(v___x_103_, v_a_94_);
v___x_105_ = lean_array_push(v___x_104_, v_a_97_);
v___x_106_ = 0;
v___x_107_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_107_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_107_, 1, v___x_106_);
lean_ctor_set_uint8(v___x_107_, 2, v___x_106_);
lean_ctor_set_uint8(v___x_107_, 3, v___x_106_);
v___x_108_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_105_, v___x_107_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_108_);
v___x_110_ = v___x_100_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_a_98_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
else
{
lean_dec(v_a_94_);
return v___x_96_;
}
}
else
{
lean_dec(v___x_86_);
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForTestTask___boxed(lean_object* v_x_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Fmt_fmtWaitForTestTask(v_x_113_, v_a_114_, v_a_115_);
lean_dec_ref(v_a_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1(){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_123_ = l_Lean_Fmt_fmtAttribute;
v___x_124_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForTestTask___closed__1));
v___x_125_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___closed__1));
v___x_126_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtWaitForTestTask___boxed), 3, 0);
v___x_127_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_123_, v___x_124_, v___x_125_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1___boxed(lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1();
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForSync(lean_object* v_x_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForSync___closed__1));
lean_inc(v_x_137_);
v___x_141_ = l_Lean_Syntax_isOfKind(v_x_137_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_x_137_);
v___x_142_ = l_Lean_Fmt_Error_partialFormatter;
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_139_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Lean_Syntax_getArg(v_x_137_, v___x_144_);
v___x_146_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForTestTask___closed__3));
lean_inc(v___x_145_);
v___x_147_ = l_Lean_Syntax_isOfKind(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v___x_145_);
lean_dec(v_x_137_);
v___x_148_ = l_Lean_Fmt_Error_partialFormatter;
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_a_139_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v_waitTk_151_; lean_object* v___x_152_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v_waitTk_151_ = l_Lean_Syntax_getArg(v_x_137_, v___x_150_);
lean_dec(v_x_137_);
v___x_152_ = l_Lean_Fmt_fmt(v_waitTk_151_, v_a_138_, v_a_139_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
v_a_154_ = lean_ctor_get(v___x_152_, 1);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_152_, 2);
v___x_155_ = l_Lean_Fmt_fmt(v___x_145_, v_a_138_, v_a_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_171_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_a_157_ = lean_ctor_get(v___x_155_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_171_ == 0)
{
v___x_159_ = v___x_155_;
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
v___x_163_ = lean_array_push(v___x_162_, v_a_153_);
v___x_164_ = lean_array_push(v___x_163_, v_a_156_);
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_166_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_166_, 1, v___x_165_);
lean_ctor_set_uint8(v___x_166_, 2, v___x_165_);
lean_ctor_set_uint8(v___x_166_, 3, v___x_165_);
v___x_167_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_164_, v___x_166_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_167_);
v___x_169_ = v___x_159_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_a_157_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_dec(v_a_153_);
return v___x_155_;
}
}
else
{
lean_dec(v___x_145_);
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWaitForSync___boxed(lean_object* v_x_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Fmt_fmtWaitForSync(v_x_172_, v_a_173_, v_a_174_);
lean_dec_ref(v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1(){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_182_ = l_Lean_Fmt_fmtAttribute;
v___x_183_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForSync___closed__1));
v___x_184_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___closed__1));
v___x_185_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtWaitForSync___boxed), 3, 0);
v___x_186_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_182_, v___x_183_, v___x_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1___boxed(lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1();
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBlockUntilCancelled(lean_object* v_x_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_Fmt_fmtBlockUntilCancelled___closed__1));
lean_inc(v_x_196_);
v___x_200_ = l_Lean_Syntax_isOfKind(v_x_196_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_x_196_);
v___x_201_ = l_Lean_Fmt_Error_partialFormatter;
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_198_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = l_Lean_Syntax_getArg(v_x_196_, v___x_203_);
v___x_205_ = ((lean_object*)(l_Lean_Fmt_fmtWaitForTestTask___closed__3));
lean_inc(v___x_204_);
v___x_206_ = l_Lean_Syntax_isOfKind(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v___x_204_);
lean_dec(v_x_196_);
v___x_207_ = l_Lean_Fmt_Error_partialFormatter;
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_a_198_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v_blockTk_210_; lean_object* v___x_211_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v_blockTk_210_ = l_Lean_Syntax_getArg(v_x_196_, v___x_209_);
lean_dec(v_x_196_);
v___x_211_ = l_Lean_Fmt_fmt(v_blockTk_210_, v_a_197_, v_a_198_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_a_213_; lean_object* v___x_214_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
v_a_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_211_, 2);
v___x_214_ = l_Lean_Fmt_fmt(v___x_204_, v_a_197_, v_a_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_230_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_a_216_ = lean_ctor_get(v___x_214_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_230_ == 0)
{
v___x_218_ = v___x_214_;
v_isShared_219_ = v_isSharedCheck_230_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_230_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_220_ = lean_unsigned_to_nat(2u);
v___x_221_ = lean_mk_empty_array_with_capacity(v___x_220_);
v___x_222_ = lean_array_push(v___x_221_, v_a_212_);
v___x_223_ = lean_array_push(v___x_222_, v_a_215_);
v___x_224_ = 0;
v___x_225_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_225_, 0, v___x_206_);
lean_ctor_set_uint8(v___x_225_, 1, v___x_224_);
lean_ctor_set_uint8(v___x_225_, 2, v___x_224_);
lean_ctor_set_uint8(v___x_225_, 3, v___x_224_);
v___x_226_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_223_, v___x_225_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_226_);
v___x_228_ = v___x_218_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_a_216_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
else
{
lean_dec(v_a_212_);
return v___x_214_;
}
}
else
{
lean_dec(v___x_204_);
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBlockUntilCancelled___boxed(lean_object* v_x_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Fmt_fmtBlockUntilCancelled(v_x_231_, v_a_232_, v_a_233_);
lean_dec_ref(v_a_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1(){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_241_ = l_Lean_Fmt_fmtAttribute;
v___x_242_ = ((lean_object*)(l_Lean_Fmt_fmtBlockUntilCancelled___closed__1));
v___x_243_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___closed__1));
v___x_244_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBlockUntilCancelled___boxed), 3, 0);
v___x_245_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_241_, v___x_242_, v___x_243_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1___boxed(lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1();
return v_res_247_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Server_Test_Cancel(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForCancelOnceCommand___regBuiltin_Lean_Fmt_fmtWaitForCancelOnceCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForTestTask___regBuiltin_Lean_Fmt_fmtWaitForTestTask__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtWaitForSync___regBuiltin_Lean_Fmt_fmtWaitForSync__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Server_Test_Cancel_0__Lean_Fmt_fmtBlockUntilCancelled___regBuiltin_Lean_Fmt_fmtBlockUntilCancelled__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Server_Test_Cancel(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Server_Test_Cancel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Server_Test_Cancel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Server_Test_Cancel(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Server_Test_Cancel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Test_Cancel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Server_Test_Cancel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Server_Test_Cancel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Server_Test_Cancel(builtin);
}
#ifdef __cplusplus
}
#endif
