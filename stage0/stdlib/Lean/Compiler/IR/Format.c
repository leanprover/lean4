// Lean compiler output
// Module: Lean.Compiler.IR.Format
// Imports: public import Lean.Compiler.IR.Basic import Init.Data.Format.Macro
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
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_String_quote(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "x_"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "◾"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatArg___private__1(lean_object*);
static const lean_closure_object l_Lean_IR_instToFormatArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToFormatArg___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToFormatArg___closed__0 = (const lean_object*)&l_Lean_IR_instToFormatArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToFormatArg = (const lean_object*)&l_Lean_IR_instToFormatArg___closed__0_value;
static const lean_string_object l_Lean_IR_formatArray___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_IR_formatArray___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_IR_formatArray___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_IR_formatArray___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatArray___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_IR_formatArray___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_IR_formatArray___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_formatArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_formatArray___redArg___closed__0 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__0_value;
static const lean_closure_object l_Lean_IR_formatArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_formatArray___redArg___closed__1 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__1_value;
static const lean_closure_object l_Lean_IR_formatArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_formatArray___redArg___closed__2 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__2_value;
static const lean_closure_object l_Lean_IR_formatArray___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_formatArray___redArg___closed__3 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__3_value;
static const lean_closure_object l_Lean_IR_formatArray___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_formatArray___redArg___closed__4 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__4_value;
static const lean_closure_object l_Lean_IR_formatArray___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_formatArray___redArg___closed__5 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__5_value;
static const lean_closure_object l_Lean_IR_formatArray___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_formatArray___redArg___closed__6 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__6_value;
static const lean_ctor_object l_Lean_IR_formatArray___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_formatArray___redArg___closed__0_value),((lean_object*)&l_Lean_IR_formatArray___redArg___closed__1_value)}};
static const lean_object* l_Lean_IR_formatArray___redArg___closed__7 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__7_value;
static const lean_ctor_object l_Lean_IR_formatArray___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_formatArray___redArg___closed__7_value),((lean_object*)&l_Lean_IR_formatArray___redArg___closed__2_value),((lean_object*)&l_Lean_IR_formatArray___redArg___closed__3_value),((lean_object*)&l_Lean_IR_formatArray___redArg___closed__4_value),((lean_object*)&l_Lean_IR_formatArray___redArg___closed__5_value)}};
static const lean_object* l_Lean_IR_formatArray___redArg___closed__8 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__8_value;
static const lean_ctor_object l_Lean_IR_formatArray___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_formatArray___redArg___closed__8_value),((lean_object*)&l_Lean_IR_formatArray___redArg___closed__6_value)}};
static const lean_object* l_Lean_IR_formatArray___redArg___closed__9 = (const lean_object*)&l_Lean_IR_formatArray___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatLitVal___private__1(lean_object*);
static const lean_closure_object l_Lean_IR_instToFormatLitVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToFormatLitVal___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToFormatLitVal___closed__0 = (const lean_object*)&l_Lean_IR_instToFormatLitVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToFormatLitVal = (const lean_object*)&l_Lean_IR_instToFormatLitVal___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctor_"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatCtorInfo___private__1(lean_object*);
static const lean_closure_object l_Lean_IR_instToFormatCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToFormatCtorInfo___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToFormatCtorInfo___closed__0 = (const lean_object*)&l_Lean_IR_instToFormatCtorInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToFormatCtorInfo = (const lean_object*)&l_Lean_IR_instToFormatCtorInfo___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reset["};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proj["};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "uproj["};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sproj["};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pap "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "app "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "box "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unbox "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "isShared "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatExpr___private__1(lean_object*);
static const lean_closure_object l_Lean_IR_instToFormatExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToFormatExpr___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToFormatExpr___closed__0 = (const lean_object*)&l_Lean_IR_instToFormatExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToFormatExpr = (const lean_object*)&l_Lean_IR_instToFormatExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringExpr___lam__0(lean_object*);
static const lean_closure_object l_Lean_IR_instToStringExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToStringExpr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToStringExpr___closed__0 = (const lean_object*)&l_Lean_IR_instToStringExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToStringExpr = (const lean_object*)&l_Lean_IR_instToStringExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "float"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "u8"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "u16"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "u32"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "u64"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "usize"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "float32"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "struct "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22;
static lean_once_cell_t l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "union "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "void"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatIRType___private__1(lean_object*);
static const lean_closure_object l_Lean_IR_instToFormatIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToFormatIRType___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToFormatIRType___closed__0 = (const lean_object*)&l_Lean_IR_instToFormatIRType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToFormatIRType = (const lean_object*)&l_Lean_IR_instToFormatIRType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringIRType___lam__0(lean_object*);
static const lean_closure_object l_Lean_IR_instToStringIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToStringIRType___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToStringIRType___closed__0 = (const lean_object*)&l_Lean_IR_instToStringIRType___closed__0_value;
static const lean_closure_object l_Lean_IR_instToStringIRType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_instToStringIRType___closed__0_value),((lean_object*)&l_Lean_IR_instToFormatIRType___closed__0_value)} };
static const lean_object* l_Lean_IR_instToStringIRType___closed__1 = (const lean_object*)&l_Lean_IR_instToStringIRType___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToStringIRType = (const lean_object*)&l_Lean_IR_instToStringIRType___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "@& "};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatParam___private__1(lean_object*);
static const lean_closure_object l_Lean_IR_instToFormatParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToFormatParam___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToFormatParam___closed__0 = (const lean_object*)&l_Lean_IR_instToFormatParam___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToFormatParam = (const lean_object*)&l_Lean_IR_instToFormatParam___closed__0_value;
static const lean_string_object l_Lean_IR_formatAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = " →"};
static const lean_object* l_Lean_IR_formatAlt___closed__0 = (const lean_object*)&l_Lean_IR_formatAlt___closed__0_value;
static const lean_ctor_object l_Lean_IR_formatAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatAlt___closed__0_value)}};
static const lean_object* l_Lean_IR_formatAlt___closed__1 = (const lean_object*)&l_Lean_IR_formatAlt___closed__1_value;
static const lean_string_object l_Lean_IR_formatAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "default →"};
static const lean_object* l_Lean_IR_formatAlt___closed__2 = (const lean_object*)&l_Lean_IR_formatAlt___closed__2_value;
static const lean_ctor_object l_Lean_IR_formatAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatAlt___closed__2_value)}};
static const lean_object* l_Lean_IR_formatAlt___closed__3 = (const lean_object*)&l_Lean_IR_formatAlt___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_IR_formatAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatParams___boxed(lean_object*);
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "let "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__0 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__0_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__0_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__1 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__1_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__2 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__2_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__2_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__3 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__3_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "block_"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__4 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__4_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " := ..."};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__5 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__5_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__5_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__6 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__6_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "set "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__7 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__7_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__7_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__8 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__8_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "] := "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__9 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__9_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__9_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__10 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__10_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "setTag "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__11 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__11_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__11_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__12 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__12_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "uset "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__13 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__13_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__13_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__14 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__14_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sset "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__15 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__15_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__15_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__16 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__16_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "] : "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__17 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__17_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__17_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__18 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__18_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inc"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__19 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__19_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__19_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__20 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__20_value;
static lean_once_cell_t l_Lean_IR_formatFnBodyHead___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_formatFnBodyHead___closed__21;
static lean_once_cell_t l_Lean_IR_formatFnBodyHead___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_formatFnBodyHead___closed__22;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__23 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__23_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__24 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__24_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__24_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__25 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__25_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "del "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__26 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__26_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__26_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__27 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__27_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__28 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__28_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__28_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__29 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__29_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " of ..."};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__30 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__30_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__30_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__31 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__31_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ret "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__32 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__32_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__32_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__33 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__33_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "jmp "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__34 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__34_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__34_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__35 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__35_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊥"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__36 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__36_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__36_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__37 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__37_value;
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBodyHead(lean_object*);
LEAN_EXPORT lean_object* lean_ir_format_fn_body_head(lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " :="};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " of"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatFnBody___lam__0(lean_object*);
static const lean_closure_object l_Lean_IR_instToFormatFnBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToFormatFnBody___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToFormatFnBody___closed__0 = (const lean_object*)&l_Lean_IR_instToFormatFnBody___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToFormatFnBody = (const lean_object*)&l_Lean_IR_instToFormatFnBody___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringFnBody___lam__0(lean_object*);
static const lean_closure_object l_Lean_IR_instToStringFnBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToStringFnBody___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToStringFnBody___closed__0 = (const lean_object*)&l_Lean_IR_instToStringFnBody___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToStringFnBody = (const lean_object*)&l_Lean_IR_instToStringFnBody___closed__0_value;
static const lean_string_object l_Lean_IR_formatDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "def "};
static const lean_object* l_Lean_IR_formatDecl___closed__0 = (const lean_object*)&l_Lean_IR_formatDecl___closed__0_value;
static const lean_ctor_object l_Lean_IR_formatDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatDecl___closed__0_value)}};
static const lean_object* l_Lean_IR_formatDecl___closed__1 = (const lean_object*)&l_Lean_IR_formatDecl___closed__1_value;
static const lean_string_object l_Lean_IR_formatDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extern "};
static const lean_object* l_Lean_IR_formatDecl___closed__2 = (const lean_object*)&l_Lean_IR_formatDecl___closed__2_value;
static const lean_ctor_object l_Lean_IR_formatDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatDecl___closed__2_value)}};
static const lean_object* l_Lean_IR_formatDecl___closed__3 = (const lean_object*)&l_Lean_IR_formatDecl___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatDecl___lam__0(lean_object*);
static const lean_closure_object l_Lean_IR_instToFormatDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToFormatDecl___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToFormatDecl___closed__0 = (const lean_object*)&l_Lean_IR_instToFormatDecl___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToFormatDecl = (const lean_object*)&l_Lean_IR_instToFormatDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_declToString(lean_object*);
static const lean_closure_object l_Lean_IR_instToStringDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_declToString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToStringDecl___closed__0 = (const lean_object*)&l_Lean_IR_instToStringDecl___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToStringDecl = (const lean_object*)&l_Lean_IR_instToStringDecl___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(lean_object* v_x_5_){
_start:
{
if (lean_obj_tag(v_x_5_) == 0)
{
lean_object* v_id_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_16_; 
v_id_6_ = lean_ctor_get(v_x_5_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_5_);
if (v_isSharedCheck_16_ == 0)
{
v___x_8_ = v_x_5_;
v_isShared_9_ = v_isSharedCheck_16_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_id_6_);
lean_dec(v_x_5_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_16_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_14_; 
v___x_10_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_11_ = l_Nat_reprFast(v_id_6_);
v___x_12_ = lean_string_append(v___x_10_, v___x_11_);
lean_dec_ref(v___x_11_);
if (v_isShared_9_ == 0)
{
lean_ctor_set_tag(v___x_8_, 3);
lean_ctor_set(v___x_8_, 0, v___x_12_);
v___x_14_ = v___x_8_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v___x_12_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v___x_17_; 
v___x_17_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2));
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatArg___private__1(lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_a_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___redArg___lam__0(lean_object* v_inst_25_, lean_object* v_x1_26_, lean_object* v_x2_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_28_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_29_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_29_, 0, v_x1_26_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = lean_apply_1(v_inst_25_, v_x2_27_);
v___x_31_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_29_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___redArg(lean_object* v_inst_51_, lean_object* v_args_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_53_ = lean_box(0);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_array_get_size(v_args_52_);
v___x_56_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___closed__9));
v___x_57_ = lean_nat_dec_lt(v___x_54_, v___x_55_);
if (v___x_57_ == 0)
{
lean_dec_ref(v_args_52_);
lean_dec_ref(v_inst_51_);
return v___x_53_;
}
else
{
lean_object* v___f_58_; size_t v___x_59_; size_t v___x_60_; lean_object* v___x_61_; 
v___f_58_ = lean_alloc_closure((void*)(l_Lean_IR_formatArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_58_, 0, v_inst_51_);
v___x_59_ = ((size_t)0ULL);
v___x_60_ = lean_usize_of_nat(v___x_55_);
v___x_61_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_56_, v___f_58_, v_args_52_, v___x_59_, v___x_60_, v___x_53_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_args_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_IR_formatArray___redArg(v_inst_63_, v_args_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v_v_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_v_67_ = lean_ctor_get(v_x_66_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_75_ == 0)
{
v___x_69_ = v_x_66_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_v_67_);
lean_dec(v_x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = l_Nat_reprFast(v_v_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 3);
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
else
{
lean_object* v_v_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_v_76_ = lean_ctor_get(v_x_66_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v_x_66_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_v_76_);
lean_dec(v_x_66_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = l_String_quote(v_v_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 3);
lean_ctor_set(v___x_78_, 0, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatLitVal___private__1(lean_object* v_a_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(v_a_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(lean_object* v_x_101_){
_start:
{
lean_object* v_name_102_; lean_object* v_cidx_103_; lean_object* v_usize_104_; lean_object* v_ssize_105_; lean_object* v_r_107_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_r_121_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_name_102_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_name_102_);
v_cidx_103_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_cidx_103_);
v_usize_104_ = lean_ctor_get(v_x_101_, 3);
lean_inc(v_usize_104_);
v_ssize_105_ = lean_ctor_get(v_x_101_, 4);
lean_inc(v_ssize_105_);
lean_dec_ref(v_x_101_);
v___x_118_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5));
v___x_119_ = l_Nat_reprFast(v_cidx_103_);
v___x_120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
v_r_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_121_, 0, v___x_118_);
lean_ctor_set(v_r_121_, 1, v___x_120_);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_nat_dec_lt(v___x_132_, v_usize_104_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_lt(v___x_132_, v_ssize_105_);
if (v___x_134_ == 0)
{
lean_dec(v_ssize_105_);
lean_dec(v_usize_104_);
v_r_107_ = v_r_121_;
goto v___jp_106_;
}
else
{
goto v___jp_122_;
}
}
else
{
goto v___jp_122_;
}
v___jp_106_:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_box(0);
v___x_109_ = lean_name_eq(v_name_102_, v___x_108_);
if (v___x_109_ == 0)
{
uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_r_117_; 
v___x_110_ = 1;
v___x_111_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v_r_107_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = l_Lean_Name_toString(v_name_102_, v___x_110_);
v___x_114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
v___x_115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_112_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v_r_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_117_, 0, v___x_115_);
lean_ctor_set(v_r_117_, 1, v___x_116_);
return v_r_117_;
}
else
{
lean_dec(v_name_102_);
return v_r_107_;
}
}
v___jp_122_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_r_131_; 
v___x_123_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7));
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v_r_121_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = l_Nat_reprFast(v_usize_104_);
v___x_126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_124_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_123_);
v___x_129_ = l_Nat_reprFast(v_ssize_105_);
v___x_130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
v_r_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_131_, 0, v___x_128_);
lean_ctor_set(v_r_131_, 1, v___x_130_);
v_r_107_ = v_r_131_;
goto v___jp_106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatCtorInfo___private__1(lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_a_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(lean_object* v_as_139_, size_t v_i_140_, size_t v_stop_141_, lean_object* v_b_142_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = lean_usize_dec_eq(v_i_140_, v_stop_141_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; size_t v___x_149_; size_t v___x_150_; 
v___x_144_ = lean_array_uget_borrowed(v_as_139_, v_i_140_);
v___x_145_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v_b_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_inc(v___x_144_);
v___x_147_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v___x_144_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_add(v_i_140_, v___x_149_);
v_i_140_ = v___x_150_;
v_b_142_ = v___x_148_;
goto _start;
}
else
{
return v_b_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0___boxed(lean_object* v_as_152_, lean_object* v_i_153_, lean_object* v_stop_154_, lean_object* v_b_155_){
_start:
{
size_t v_i_boxed_156_; size_t v_stop_boxed_157_; lean_object* v_res_158_; 
v_i_boxed_156_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_stop_boxed_157_ = lean_unbox_usize(v_stop_154_);
lean_dec(v_stop_154_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_as_152_, v_i_boxed_156_, v_stop_boxed_157_, v_b_155_);
lean_dec_ref(v_as_152_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(lean_object* v_args_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_160_ = lean_box(0);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get_size(v_args_159_);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
return v___x_160_;
}
else
{
size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; 
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_162_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_159_, v___x_164_, v___x_165_, v___x_160_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(lean_object* v_args_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_args_167_);
lean_dec_ref(v_args_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(lean_object* v_x_210_){
_start:
{
switch(lean_obj_tag(v_x_210_))
{
case 0:
{
lean_object* v_i_211_; lean_object* v_ys_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_221_; 
v_i_211_ = lean_ctor_get(v_x_210_, 0);
v_ys_212_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_221_ == 0)
{
v___x_214_ = v_x_210_;
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_ys_212_);
lean_inc(v_i_211_);
lean_dec(v_x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_211_);
v___x_217_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_212_);
lean_dec_ref(v_ys_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 5);
lean_ctor_set(v___x_214_, 1, v___x_217_);
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_219_ = v___x_214_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
case 1:
{
lean_object* v_n_222_; lean_object* v_x_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_240_; 
v_n_222_ = lean_ctor_get(v_x_210_, 0);
v_x_223_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_240_ == 0)
{
v___x_225_ = v_x_210_;
v_isShared_226_ = v_isSharedCheck_240_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_x_223_);
lean_inc(v_n_222_);
lean_dec(v_x_210_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_240_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_227_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1));
v___x_228_ = l_Nat_reprFast(v_n_222_);
v___x_229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 5);
lean_ctor_set(v___x_225_, 1, v___x_229_);
lean_ctor_set(v___x_225_, 0, v___x_227_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_239_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_232_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_235_ = l_Nat_reprFast(v_x_223_);
v___x_236_ = lean_string_append(v___x_234_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_233_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
}
}
case 2:
{
lean_object* v_x_241_; lean_object* v_i_242_; uint8_t v_updtHeader_243_; lean_object* v_ys_244_; lean_object* v___x_245_; lean_object* v___y_247_; 
v_x_241_ = lean_ctor_get(v_x_210_, 0);
lean_inc(v_x_241_);
v_i_242_ = lean_ctor_get(v_x_210_, 1);
lean_inc_ref(v_i_242_);
v_updtHeader_243_ = lean_ctor_get_uint8(v_x_210_, sizeof(void*)*3);
v_ys_244_ = lean_ctor_get(v_x_210_, 2);
lean_inc_ref(v_ys_244_);
lean_dec_ref_known(v_x_210_, 3);
v___x_245_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5));
if (v_updtHeader_243_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8));
v___y_247_ = v___x_263_;
goto v___jp_246_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9));
v___y_247_ = v___x_264_;
goto v___jp_246_;
}
v___jp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
lean_inc_ref(v___y_247_);
v___x_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_248_, 0, v___y_247_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_245_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_253_ = l_Nat_reprFast(v_x_241_);
v___x_254_ = lean_string_append(v___x_252_, v___x_253_);
lean_dec_ref(v___x_253_);
v___x_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_251_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7));
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_242_);
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_244_);
lean_dec_ref(v_ys_244_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
return v___x_262_;
}
}
case 3:
{
lean_object* v_i_265_; lean_object* v_x_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_283_; 
v_i_265_ = lean_ctor_get(v_x_210_, 0);
v_x_266_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_283_ == 0)
{
v___x_268_ = v_x_210_;
v_isShared_269_ = v_isSharedCheck_283_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_x_266_);
lean_inc(v_i_265_);
lean_dec(v_x_210_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_283_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11));
v___x_271_ = l_Nat_reprFast(v_i_265_);
v___x_272_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 5);
lean_ctor_set(v___x_268_, 1, v___x_272_);
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_274_ = v___x_268_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_282_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_278_ = l_Nat_reprFast(v_x_266_);
v___x_279_ = lean_string_append(v___x_277_, v___x_278_);
lean_dec_ref(v___x_278_);
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
v___x_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_276_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
return v___x_281_;
}
}
}
case 4:
{
lean_object* v_i_284_; lean_object* v_x_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_302_; 
v_i_284_ = lean_ctor_get(v_x_210_, 0);
v_x_285_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_302_ == 0)
{
v___x_287_ = v_x_210_;
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_x_285_);
lean_inc(v_i_284_);
lean_dec(v_x_210_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13));
v___x_290_ = l_Nat_reprFast(v_i_284_);
v___x_291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 5);
lean_ctor_set(v___x_287_, 1, v___x_291_);
lean_ctor_set(v___x_287_, 0, v___x_289_);
v___x_293_ = v___x_287_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_291_);
v___x_293_ = v_reuseFailAlloc_301_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_294_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_297_ = l_Nat_reprFast(v_x_285_);
v___x_298_ = lean_string_append(v___x_296_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
v___x_300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_295_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
return v___x_300_;
}
}
}
case 5:
{
lean_object* v_n_303_; lean_object* v_offset_304_; lean_object* v_x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_n_303_ = lean_ctor_get(v_x_210_, 0);
lean_inc(v_n_303_);
v_offset_304_ = lean_ctor_get(v_x_210_, 1);
lean_inc(v_offset_304_);
v_x_305_ = lean_ctor_get(v_x_210_, 2);
lean_inc(v_x_305_);
lean_dec_ref_known(v_x_210_, 3);
v___x_306_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15));
v___x_307_ = l_Nat_reprFast(v_n_303_);
v___x_308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_306_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = l_Nat_reprFast(v_offset_304_);
v___x_313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_311_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_318_ = l_Nat_reprFast(v_x_305_);
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
lean_dec_ref(v___x_318_);
v___x_320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_316_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
return v___x_321_;
}
case 6:
{
lean_object* v_c_322_; lean_object* v_ys_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_334_; 
v_c_322_ = lean_ctor_get(v_x_210_, 0);
v_ys_323_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_334_ == 0)
{
v___x_325_ = v_x_210_;
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_ys_323_);
lean_inc(v_c_322_);
lean_dec(v_x_210_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_327_ = 1;
v___x_328_ = l_Lean_Name_toString(v_c_322_, v___x_327_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
v___x_330_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_323_);
lean_dec_ref(v_ys_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 5);
lean_ctor_set(v___x_325_, 1, v___x_330_);
lean_ctor_set(v___x_325_, 0, v___x_329_);
v___x_332_ = v___x_325_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
case 7:
{
lean_object* v_c_335_; lean_object* v_ys_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_349_; 
v_c_335_ = lean_ctor_get(v_x_210_, 0);
v_ys_336_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_349_ == 0)
{
v___x_338_ = v_x_210_;
v_isShared_339_ = v_isSharedCheck_349_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_ys_336_);
lean_inc(v_c_335_);
lean_dec(v_x_210_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_349_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19));
v___x_341_ = 1;
v___x_342_ = l_Lean_Name_toString(v_c_335_, v___x_341_);
v___x_343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 5);
lean_ctor_set(v___x_338_, 1, v___x_343_);
lean_ctor_set(v___x_338_, 0, v___x_340_);
v___x_345_ = v___x_338_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_343_);
v___x_345_ = v_reuseFailAlloc_348_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_336_);
lean_dec_ref(v_ys_336_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
}
}
case 8:
{
lean_object* v_x_350_; lean_object* v_ys_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_365_; 
v_x_350_ = lean_ctor_get(v_x_210_, 0);
v_ys_351_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_365_ == 0)
{
v___x_353_ = v_x_210_;
v_isShared_354_ = v_isSharedCheck_365_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_ys_351_);
lean_inc(v_x_350_);
lean_dec(v_x_210_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_365_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_355_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21));
v___x_356_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_357_ = l_Nat_reprFast(v_x_350_);
v___x_358_ = lean_string_append(v___x_356_, v___x_357_);
lean_dec_ref(v___x_357_);
v___x_359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 5);
lean_ctor_set(v___x_353_, 1, v___x_359_);
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_361_ = v___x_353_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_364_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_351_);
lean_dec_ref(v_ys_351_);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
return v___x_363_;
}
}
}
case 9:
{
lean_object* v_x_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_378_; 
v_x_366_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v_x_210_, 0);
lean_dec(v_unused_379_);
v___x_368_ = v_x_210_;
v_isShared_369_ = v_isSharedCheck_378_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_x_366_);
lean_dec(v_x_210_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_378_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23));
v___x_371_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_372_ = l_Nat_reprFast(v_x_366_);
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
lean_dec_ref(v___x_372_);
v___x_374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 5);
lean_ctor_set(v___x_368_, 1, v___x_374_);
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_376_ = v___x_368_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
case 10:
{
lean_object* v_x_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_392_; 
v_x_380_ = lean_ctor_get(v_x_210_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_392_ == 0)
{
v___x_382_ = v_x_210_;
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_x_380_);
lean_dec(v_x_210_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25));
v___x_385_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_386_ = l_Nat_reprFast(v_x_380_);
v___x_387_ = lean_string_append(v___x_385_, v___x_386_);
lean_dec_ref(v___x_386_);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 3);
lean_ctor_set(v___x_382_, 0, v___x_387_);
v___x_389_ = v___x_382_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_391_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_384_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
return v___x_390_;
}
}
}
case 11:
{
lean_object* v_v_393_; lean_object* v___x_394_; 
v_v_393_ = lean_ctor_get(v_x_210_, 0);
lean_inc_ref(v_v_393_);
lean_dec_ref_known(v_x_210_, 1);
v___x_394_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(v_v_393_);
return v___x_394_;
}
default: 
{
lean_object* v_x_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_407_; 
v_x_395_ = lean_ctor_get(v_x_210_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_407_ == 0)
{
v___x_397_ = v_x_210_;
v_isShared_398_ = v_isSharedCheck_407_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_x_395_);
lean_dec(v_x_210_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_407_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_399_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27));
v___x_400_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_401_ = l_Nat_reprFast(v_x_395_);
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
lean_dec_ref(v___x_401_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 3);
lean_ctor_set(v___x_397_, 0, v___x_402_);
v___x_404_ = v___x_397_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_406_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_399_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatExpr___private__1(lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_a_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringExpr___lam__0(lean_object* v_e_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_412_);
v___x_414_ = l_Std_Format_defWidth;
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = l_Std_Format_pretty(v___x_413_, v___x_414_, v___x_415_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__1(lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_nat_to_int(v_a_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_453_; 
lean_dec(v_x_452_);
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v_tail_454_; 
v_tail_454_ = lean_ctor_get(v_x_451_, 1);
if (lean_obj_tag(v_tail_454_) == 0)
{
lean_object* v_head_455_; lean_object* v___x_456_; 
lean_dec(v_x_452_);
v_head_455_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_head_455_);
lean_dec_ref_known(v_x_451_, 2);
v___x_456_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_455_);
return v___x_456_;
}
else
{
lean_object* v_head_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_inc(v_tail_454_);
v_head_457_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_head_457_);
lean_dec_ref_known(v_x_451_, 2);
v___x_458_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_457_);
v___x_459_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(v_x_452_, v___x_458_, v_tail_454_);
return v___x_459_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20));
v___x_462_ = lean_string_length(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22);
v___x_464_ = lean_nat_to_int(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object* v_x_479_){
_start:
{
switch(lean_obj_tag(v_x_479_))
{
case 0:
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1));
return v___x_480_;
}
case 1:
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3));
return v___x_481_;
}
case 2:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5));
return v___x_482_;
}
case 3:
{
lean_object* v___x_483_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7));
return v___x_483_;
}
case 4:
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9));
return v___x_484_;
}
case 5:
{
lean_object* v___x_485_; 
v___x_485_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11));
return v___x_485_;
}
case 6:
{
lean_object* v___x_486_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2));
return v___x_486_;
}
case 7:
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13));
return v___x_487_;
}
case 8:
{
lean_object* v___x_488_; 
v___x_488_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15));
return v___x_488_;
}
case 9:
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17));
return v___x_489_;
}
case 10:
{
lean_object* v_types_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_509_; 
v_types_490_ = lean_ctor_get(v_x_479_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v_x_479_, 0);
lean_dec(v_unused_510_);
v___x_492_ = v_x_479_;
v_isShared_493_ = v_isSharedCheck_509_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_types_490_);
lean_dec(v_x_479_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_509_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_494_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19));
v___x_495_ = lean_array_to_list(v_types_490_);
v___x_496_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_497_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_495_, v___x_496_);
v___x_498_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
v___x_499_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24));
if (v_isShared_493_ == 0)
{
lean_ctor_set_tag(v___x_492_, 5);
lean_ctor_set(v___x_492_, 1, v___x_497_);
lean_ctor_set(v___x_492_, 0, v___x_499_);
v___x_501_ = v___x_492_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_497_);
v___x_501_ = v_reuseFailAlloc_508_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25));
v___x_503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_498_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = 0;
v___x_506_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*1, v___x_505_);
v___x_507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_494_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
return v___x_507_;
}
}
}
case 11:
{
lean_object* v_types_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_530_; 
v_types_511_ = lean_ctor_get(v_x_479_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_x_479_, 0);
lean_dec(v_unused_531_);
v___x_513_ = v_x_479_;
v_isShared_514_ = v_isSharedCheck_530_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_types_511_);
lean_dec(v_x_479_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_530_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_515_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27));
v___x_516_ = lean_array_to_list(v_types_511_);
v___x_517_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_518_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_516_, v___x_517_);
v___x_519_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
v___x_520_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24));
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 5);
lean_ctor_set(v___x_513_, 1, v___x_518_);
lean_ctor_set(v___x_513_, 0, v___x_520_);
v___x_522_ = v___x_513_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_518_);
v___x_522_ = v_reuseFailAlloc_529_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_523_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25));
v___x_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_519_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = 0;
v___x_527_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*1, v___x_526_);
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_515_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
}
}
case 12:
{
lean_object* v___x_532_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29));
return v___x_532_;
}
default: 
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31));
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_dec(v_x_534_);
return v_x_535_;
}
else
{
lean_object* v_head_537_; lean_object* v_tail_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_548_; 
v_head_537_ = lean_ctor_get(v_x_536_, 0);
v_tail_538_ = lean_ctor_get(v_x_536_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_548_ == 0)
{
v___x_540_ = v_x_536_;
v_isShared_541_ = v_isSharedCheck_548_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_tail_538_);
lean_inc(v_head_537_);
lean_dec(v_x_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_548_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
lean_inc(v_x_534_);
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 5);
lean_ctor_set(v___x_540_, 1, v_x_534_);
lean_ctor_set(v___x_540_, 0, v_x_535_);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_x_535_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_x_534_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_537_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v_x_535_ = v___x_545_;
v_x_536_ = v_tail_538_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatIRType___private__1(lean_object* v_a_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringIRType___lam__0(lean_object* v_f_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = l_Std_Format_defWidth;
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l_Std_Format_pretty(v_f_553_, v___x_554_, v___x_555_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(lean_object* v_x_572_){
_start:
{
lean_object* v_x_573_; uint8_t v_borrow_574_; lean_object* v_ty_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___y_585_; 
v_x_573_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_x_573_);
v_borrow_574_ = lean_ctor_get_uint8(v_x_572_, sizeof(void*)*2);
v_ty_575_ = lean_ctor_get(v_x_572_, 1);
lean_inc(v_ty_575_);
lean_dec_ref(v_x_572_);
v___x_576_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1));
v___x_577_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_578_ = l_Nat_reprFast(v_x_573_);
v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
lean_dec_ref(v___x_578_);
v___x_580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___x_581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_576_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
if (v_borrow_574_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8));
v___y_585_ = v___x_592_;
goto v___jp_584_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6));
v___y_585_ = v___x_593_;
goto v___jp_584_;
}
v___jp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_inc_ref(v___y_585_);
v___x_586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_586_, 0, v___y_585_);
v___x_587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_583_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_575_);
v___x_589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5));
v___x_591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatParam___private__1(lean_object* v_a_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v_a_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatAlt(lean_object* v_fmt_604_, lean_object* v_indent_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v_info_607_; lean_object* v_b_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_626_; 
v_info_607_ = lean_ctor_get(v_x_606_, 0);
v_b_608_ = lean_ctor_get(v_x_606_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_606_);
if (v_isSharedCheck_626_ == 0)
{
v___x_610_ = v_x_606_;
v_isShared_611_ = v_isSharedCheck_626_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_b_608_);
lean_inc(v_info_607_);
lean_dec(v_x_606_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_626_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_name_612_; uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v_name_612_ = lean_ctor_get(v_info_607_, 0);
lean_inc(v_name_612_);
lean_dec_ref(v_info_607_);
v___x_613_ = 1;
v___x_614_ = l_Lean_Name_toString(v_name_612_, v___x_613_);
v___x_615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_IR_formatAlt___closed__1));
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 5);
lean_ctor_set(v___x_610_, 1, v___x_616_);
lean_ctor_set(v___x_610_, 0, v___x_615_);
v___x_618_ = v___x_610_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_616_);
v___x_618_ = v_reuseFailAlloc_625_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_619_ = lean_nat_to_int(v_indent_605_);
v___x_620_ = lean_box(1);
v___x_621_ = lean_apply_1(v_fmt_604_, v_b_608_);
v___x_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_619_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_618_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
return v___x_624_;
}
}
}
else
{
lean_object* v_b_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_b_627_ = lean_ctor_get(v_x_606_, 0);
lean_inc(v_b_627_);
lean_dec_ref_known(v_x_606_, 1);
v___x_628_ = ((lean_object*)(l_Lean_IR_formatAlt___closed__3));
v___x_629_ = lean_nat_to_int(v_indent_605_);
v___x_630_ = lean_box(1);
v___x_631_ = lean_apply_1(v_fmt_604_, v_b_627_);
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_629_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_628_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(lean_object* v_as_635_, size_t v_i_636_, size_t v_stop_637_, lean_object* v_b_638_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_eq(v_i_636_, v_stop_637_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; size_t v___x_645_; size_t v___x_646_; 
v___x_640_ = lean_array_uget_borrowed(v_as_635_, v_i_636_);
v___x_641_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_642_, 0, v_b_638_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_inc(v___x_640_);
v___x_643_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v___x_640_);
v___x_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = lean_usize_add(v_i_636_, v___x_645_);
v_i_636_ = v___x_646_;
v_b_638_ = v___x_644_;
goto _start;
}
else
{
return v_b_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0___boxed(lean_object* v_as_648_, lean_object* v_i_649_, lean_object* v_stop_650_, lean_object* v_b_651_){
_start:
{
size_t v_i_boxed_652_; size_t v_stop_boxed_653_; lean_object* v_res_654_; 
v_i_boxed_652_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_stop_boxed_653_ = lean_unbox_usize(v_stop_650_);
lean_dec(v_stop_650_);
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_as_648_, v_i_boxed_652_, v_stop_boxed_653_, v_b_651_);
lean_dec_ref(v_as_648_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(lean_object* v_args_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = lean_box(0);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_array_get_size(v_args_655_);
v___x_659_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
return v___x_656_;
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_658_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_655_, v___x_660_, v___x_661_, v___x_656_);
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0___boxed(lean_object* v_args_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_args_663_);
lean_dec_ref(v_args_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams(lean_object* v_ps_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_ps_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams___boxed(lean_object* v_ps_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_IR_formatParams(v_ps_667_);
lean_dec_ref(v_ps_667_);
return v_res_668_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__21(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0));
v___x_701_ = lean_string_length(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__22(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__21, &l_Lean_IR_formatFnBodyHead___closed__21_once, _init_l_Lean_IR_formatFnBodyHead___closed__21);
v___x_703_ = lean_nat_to_int(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBodyHead(lean_object* v_x_727_){
_start:
{
switch(lean_obj_tag(v_x_727_))
{
case 0:
{
lean_object* v_x_728_; lean_object* v_ty_729_; lean_object* v_e_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_x_728_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_x_728_);
v_ty_729_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_ty_729_);
v_e_730_ = lean_ctor_get(v_x_727_, 2);
lean_inc_ref(v_e_730_);
lean_dec_ref_known(v_x_727_, 4);
v___x_731_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__1));
v___x_732_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_733_ = l_Nat_reprFast(v_x_728_);
v___x_734_ = lean_string_append(v___x_732_, v___x_733_);
lean_dec_ref(v___x_733_);
v___x_735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_731_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_729_);
v___x_740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_730_);
v___x_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
return v___x_744_;
}
case 1:
{
lean_object* v_j_745_; lean_object* v_xs_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_j_745_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_j_745_);
v_xs_746_ = lean_ctor_get(v_x_727_, 1);
lean_inc_ref(v_xs_746_);
lean_dec_ref_known(v_x_727_, 4);
v___x_747_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_748_ = l_Nat_reprFast(v_j_745_);
v___x_749_ = lean_string_append(v___x_747_, v___x_748_);
lean_dec_ref(v___x_748_);
v___x_750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
v___x_751_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_746_);
lean_dec_ref(v_xs_746_);
v___x_752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
return v___x_754_;
}
case 2:
{
lean_object* v_x_755_; lean_object* v_i_756_; lean_object* v_y_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_x_755_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_x_755_);
v_i_756_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_i_756_);
v_y_757_ = lean_ctor_get(v_x_727_, 2);
lean_inc(v_y_757_);
lean_dec_ref_known(v_x_727_, 4);
v___x_758_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__8));
v___x_759_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_760_ = l_Nat_reprFast(v_x_755_);
v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
lean_dec_ref(v___x_760_);
v___x_762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_758_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Nat_reprFast(v_i_756_);
v___x_767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
v___x_768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_765_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_757_);
v___x_772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
return v___x_772_;
}
case 3:
{
lean_object* v_x_773_; lean_object* v_cidx_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_x_773_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_x_773_);
v_cidx_774_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_cidx_774_);
lean_dec_ref_known(v_x_727_, 3);
v___x_775_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__12));
v___x_776_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_777_ = l_Nat_reprFast(v_x_773_);
v___x_778_ = lean_string_append(v___x_776_, v___x_777_);
lean_dec_ref(v___x_777_);
v___x_779_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
v___x_780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_775_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Nat_reprFast(v_cidx_774_);
v___x_784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___x_785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
return v___x_785_;
}
case 4:
{
lean_object* v_x_786_; lean_object* v_i_787_; lean_object* v_y_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_x_786_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_x_786_);
v_i_787_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_i_787_);
v_y_788_ = lean_ctor_get(v_x_727_, 2);
lean_inc(v_y_788_);
lean_dec_ref_known(v_x_727_, 4);
v___x_789_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_790_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_791_ = l_Nat_reprFast(v_x_786_);
v___x_792_ = lean_string_append(v___x_790_, v___x_791_);
lean_dec_ref(v___x_791_);
v___x_793_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___x_794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_789_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Nat_reprFast(v_i_787_);
v___x_798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Nat_reprFast(v_y_788_);
v___x_803_ = lean_string_append(v___x_790_, v___x_802_);
lean_dec_ref(v___x_802_);
v___x_804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_801_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
return v___x_805_;
}
case 5:
{
lean_object* v_x_806_; lean_object* v_i_807_; lean_object* v_offset_808_; lean_object* v_y_809_; lean_object* v_ty_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_x_806_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_x_806_);
v_i_807_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_i_807_);
v_offset_808_ = lean_ctor_get(v_x_727_, 2);
lean_inc(v_offset_808_);
v_y_809_ = lean_ctor_get(v_x_727_, 3);
lean_inc(v_y_809_);
v_ty_810_ = lean_ctor_get(v_x_727_, 4);
lean_inc(v_ty_810_);
lean_dec_ref_known(v_x_727_, 6);
v___x_811_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__16));
v___x_812_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_813_ = l_Nat_reprFast(v_x_806_);
v___x_814_ = lean_string_append(v___x_812_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___x_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_811_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Nat_reprFast(v_i_807_);
v___x_820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_818_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Nat_reprFast(v_offset_808_);
v___x_825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_823_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__18));
v___x_828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_810_);
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Nat_reprFast(v_y_809_);
v___x_834_ = lean_string_append(v___x_812_, v___x_833_);
lean_dec_ref(v___x_833_);
v___x_835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_832_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
return v___x_836_;
}
case 6:
{
lean_object* v_x_837_; lean_object* v_n_838_; lean_object* v___x_839_; lean_object* v___y_841_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_x_837_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_x_837_);
v_n_838_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_n_838_);
lean_dec_ref_known(v_x_727_, 3);
v___x_839_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__20));
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_dec_eq(v_n_838_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; 
v___x_852_ = l_Nat_reprFast(v_n_838_);
v___x_853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__22, &l_Lean_IR_formatFnBodyHead___closed__22_once, _init_l_Lean_IR_formatFnBodyHead___closed__22);
v___x_855_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_853_);
v___x_857_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_854_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = 0;
v___x_861_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*1, v___x_860_);
v___y_841_ = v___x_861_;
goto v___jp_840_;
}
else
{
lean_object* v___x_862_; 
lean_dec(v_n_838_);
v___x_862_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___y_841_ = v___x_862_;
goto v___jp_840_;
}
v___jp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_839_);
lean_ctor_set(v___x_842_, 1, v___y_841_);
v___x_843_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_846_ = l_Nat_reprFast(v_x_837_);
v___x_847_ = lean_string_append(v___x_845_, v___x_846_);
lean_dec_ref(v___x_846_);
v___x_848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
v___x_849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_844_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
return v___x_849_;
}
}
case 7:
{
lean_object* v_x_863_; lean_object* v_n_864_; lean_object* v___x_865_; lean_object* v___y_867_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_x_863_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_x_863_);
v_n_864_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_n_864_);
lean_dec_ref_known(v_x_727_, 3);
v___x_865_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__25));
v___x_876_ = lean_unsigned_to_nat(1u);
v___x_877_ = lean_nat_dec_eq(v_n_864_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; 
v___x_878_ = l_Nat_reprFast(v_n_864_);
v___x_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
v___x_880_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__22, &l_Lean_IR_formatFnBodyHead___closed__22_once, _init_l_Lean_IR_formatFnBodyHead___closed__22);
v___x_881_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_879_);
v___x_883_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_880_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = 0;
v___x_887_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v___x_886_);
v___y_867_ = v___x_887_;
goto v___jp_866_;
}
else
{
lean_object* v___x_888_; 
lean_dec(v_n_864_);
v___x_888_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___y_867_ = v___x_888_;
goto v___jp_866_;
}
v___jp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_865_);
lean_ctor_set(v___x_868_, 1, v___y_867_);
v___x_869_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_872_ = l_Nat_reprFast(v_x_863_);
v___x_873_ = lean_string_append(v___x_871_, v___x_872_);
lean_dec_ref(v___x_872_);
v___x_874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_870_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
return v___x_875_;
}
}
case 8:
{
lean_object* v_x_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_901_; 
v_x_889_ = lean_ctor_get(v_x_727_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v_x_727_, 1);
lean_dec(v_unused_902_);
v___x_891_ = v_x_727_;
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_x_889_);
lean_dec(v_x_727_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_893_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__27));
v___x_894_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_895_ = l_Nat_reprFast(v_x_889_);
v___x_896_ = lean_string_append(v___x_894_, v___x_895_);
lean_dec_ref(v___x_895_);
v___x_897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 5);
lean_ctor_set(v___x_891_, 1, v___x_897_);
lean_ctor_set(v___x_891_, 0, v___x_893_);
v___x_899_ = v___x_891_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
case 9:
{
lean_object* v_x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_x_903_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_x_903_);
lean_dec_ref_known(v_x_727_, 4);
v___x_904_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__29));
v___x_905_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_906_ = l_Nat_reprFast(v_x_903_);
v___x_907_ = lean_string_append(v___x_905_, v___x_906_);
lean_dec_ref(v___x_906_);
v___x_908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_904_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__31));
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
return v___x_911_;
}
case 10:
{
lean_object* v_x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_x_912_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_x_912_);
lean_dec_ref_known(v_x_727_, 1);
v___x_913_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__33));
v___x_914_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_912_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
return v___x_915_;
}
case 11:
{
lean_object* v_j_916_; lean_object* v_ys_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_931_; 
v_j_916_ = lean_ctor_get(v_x_727_, 0);
v_ys_917_ = lean_ctor_get(v_x_727_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_931_ == 0)
{
v___x_919_ = v_x_727_;
v_isShared_920_ = v_isSharedCheck_931_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_ys_917_);
lean_inc(v_j_916_);
lean_dec(v_x_727_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_931_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_921_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__35));
v___x_922_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_923_ = l_Nat_reprFast(v_j_916_);
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
lean_dec_ref(v___x_923_);
v___x_925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 5);
lean_ctor_set(v___x_919_, 1, v___x_925_);
lean_ctor_set(v___x_919_, 0, v___x_921_);
v___x_927_ = v___x_919_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_925_);
v___x_927_ = v_reuseFailAlloc_930_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_917_);
lean_dec_ref(v_ys_917_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
return v___x_929_;
}
}
}
default: 
{
lean_object* v___x_932_; 
v___x_932_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__37));
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_format_fn_body_head(lean_object* v_fn_933_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_934_ = l_Lean_IR_formatFnBodyHead(v_fn_933_);
v___x_935_ = l_Std_Format_defWidth;
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = l_Std_Format_pretty(v___x_934_, v___x_935_, v___x_936_, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(lean_object* v_indent_947_, lean_object* v_a_948_){
_start:
{
switch(lean_obj_tag(v_a_948_))
{
case 0:
{
lean_object* v_x_949_; lean_object* v_ty_950_; lean_object* v_e_951_; lean_object* v_b_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_x_949_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_x_949_);
v_ty_950_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_ty_950_);
v_e_951_ = lean_ctor_get(v_a_948_, 2);
lean_inc_ref(v_e_951_);
v_b_952_ = lean_ctor_get(v_a_948_, 3);
lean_inc(v_b_952_);
lean_dec_ref_known(v_a_948_, 4);
v___x_953_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__1));
v___x_954_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_955_ = l_Nat_reprFast(v_x_949_);
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_953_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_950_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_951_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_box(1);
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_952_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
return v___x_972_;
}
case 1:
{
lean_object* v_j_973_; lean_object* v_xs_974_; lean_object* v_v_975_; lean_object* v_b_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_j_973_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_j_973_);
v_xs_974_ = lean_ctor_get(v_a_948_, 1);
lean_inc_ref(v_xs_974_);
v_v_975_ = lean_ctor_get(v_a_948_, 2);
lean_inc(v_v_975_);
v_b_976_ = lean_ctor_get(v_a_948_, 3);
lean_inc(v_b_976_);
lean_dec_ref_known(v_a_948_, 4);
v___x_977_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_978_ = l_Nat_reprFast(v_j_973_);
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
lean_dec_ref(v___x_978_);
v___x_980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_974_);
lean_dec_ref(v_xs_974_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
lean_inc_n(v_indent_947_, 2);
v___x_985_ = lean_nat_to_int(v_indent_947_);
v___x_986_ = lean_box(1);
v___x_987_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_v_975_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_985_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_984_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_986_);
v___x_994_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_976_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
return v___x_995_;
}
case 2:
{
lean_object* v_x_996_; lean_object* v_i_997_; lean_object* v_y_998_; lean_object* v_b_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_x_996_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_x_996_);
v_i_997_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_i_997_);
v_y_998_ = lean_ctor_get(v_a_948_, 2);
lean_inc(v_y_998_);
v_b_999_ = lean_ctor_get(v_a_948_, 3);
lean_inc(v_b_999_);
lean_dec_ref_known(v_a_948_, 4);
v___x_1000_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__8));
v___x_1001_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1002_ = l_Nat_reprFast(v_x_996_);
v___x_1003_ = lean_string_append(v___x_1001_, v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1000_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Nat_reprFast(v_i_997_);
v___x_1009_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_998_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_box(1);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_999_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
return v___x_1020_;
}
case 3:
{
lean_object* v_x_1021_; lean_object* v_cidx_1022_; lean_object* v_b_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_x_1021_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_x_1021_);
v_cidx_1022_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_cidx_1022_);
v_b_1023_ = lean_ctor_get(v_a_948_, 2);
lean_inc(v_b_1023_);
lean_dec_ref_known(v_a_948_, 3);
v___x_1024_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__12));
v___x_1025_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1026_ = l_Nat_reprFast(v_x_1021_);
v___x_1027_ = lean_string_append(v___x_1025_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1024_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l_Nat_reprFast(v_cidx_1022_);
v___x_1033_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1031_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_box(1);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_1023_);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
return v___x_1040_;
}
case 4:
{
lean_object* v_x_1041_; lean_object* v_i_1042_; lean_object* v_y_1043_; lean_object* v_b_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_x_1041_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_x_1041_);
v_i_1042_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_i_1042_);
v_y_1043_ = lean_ctor_get(v_a_948_, 2);
lean_inc(v_y_1043_);
v_b_1044_ = lean_ctor_get(v_a_948_, 3);
lean_inc(v_b_1044_);
lean_dec_ref_known(v_a_948_, 4);
v___x_1045_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_1046_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1047_ = l_Nat_reprFast(v_x_1041_);
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1045_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Nat_reprFast(v_i_1042_);
v___x_1054_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1052_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Nat_reprFast(v_y_1043_);
v___x_1059_ = lean_string_append(v___x_1046_, v___x_1058_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1057_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_box(1);
v___x_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_1044_);
v___x_1067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
return v___x_1067_;
}
case 5:
{
lean_object* v_x_1068_; lean_object* v_i_1069_; lean_object* v_offset_1070_; lean_object* v_y_1071_; lean_object* v_ty_1072_; lean_object* v_b_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_x_1068_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_x_1068_);
v_i_1069_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_i_1069_);
v_offset_1070_ = lean_ctor_get(v_a_948_, 2);
lean_inc(v_offset_1070_);
v_y_1071_ = lean_ctor_get(v_a_948_, 3);
lean_inc(v_y_1071_);
v_ty_1072_ = lean_ctor_get(v_a_948_, 4);
lean_inc(v_ty_1072_);
v_b_1073_ = lean_ctor_get(v_a_948_, 5);
lean_inc(v_b_1073_);
lean_dec_ref_known(v_a_948_, 6);
v___x_1074_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__16));
v___x_1075_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1076_ = l_Nat_reprFast(v_x_1068_);
v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1074_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Nat_reprFast(v_i_1069_);
v___x_1083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1081_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Nat_reprFast(v_offset_1070_);
v___x_1088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1086_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__18));
v___x_1091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1072_);
v___x_1093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Nat_reprFast(v_y_1071_);
v___x_1097_ = lean_string_append(v___x_1075_, v___x_1096_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1095_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_box(1);
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_1073_);
v___x_1105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
return v___x_1105_;
}
case 6:
{
lean_object* v_x_1106_; lean_object* v_n_1107_; lean_object* v_b_1108_; lean_object* v___x_1109_; lean_object* v___y_1111_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_x_1106_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_x_1106_);
v_n_1107_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_n_1107_);
v_b_1108_ = lean_ctor_get(v_a_948_, 2);
lean_inc(v_b_1108_);
lean_dec_ref_known(v_a_948_, 3);
v___x_1109_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__20));
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_dec_eq(v_n_1107_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1128_ = l_Nat_reprFast(v_n_1107_);
v___x_1129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
v___x_1130_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__22, &l_Lean_IR_formatFnBodyHead___closed__22_once, _init_l_Lean_IR_formatFnBodyHead___closed__22);
v___x_1131_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v___x_1129_);
v___x_1133_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_1134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1130_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = 0;
v___x_1137_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*1, v___x_1136_);
v___y_1111_ = v___x_1137_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1138_; 
lean_dec(v_n_1107_);
v___x_1138_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___y_1111_ = v___x_1138_;
goto v___jp_1110_;
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1109_);
lean_ctor_set(v___x_1112_, 1, v___y_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_1114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1116_ = l_Nat_reprFast(v_x_1106_);
v___x_1117_ = lean_string_append(v___x_1115_, v___x_1116_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1114_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_box(1);
v___x_1123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_1108_);
v___x_1125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
return v___x_1125_;
}
}
case 7:
{
lean_object* v_x_1139_; lean_object* v_n_1140_; lean_object* v_b_1141_; lean_object* v___x_1142_; lean_object* v___y_1144_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_x_1139_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_x_1139_);
v_n_1140_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_n_1140_);
v_b_1141_ = lean_ctor_get(v_a_948_, 2);
lean_inc(v_b_1141_);
lean_dec_ref_known(v_a_948_, 3);
v___x_1142_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__25));
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_nat_dec_eq(v_n_1140_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; 
v___x_1161_ = l_Nat_reprFast(v_n_1140_);
v___x_1162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
v___x_1163_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__22, &l_Lean_IR_formatFnBodyHead___closed__22_once, _init_l_Lean_IR_formatFnBodyHead___closed__22);
v___x_1164_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1162_);
v___x_1166_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1163_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = 0;
v___x_1170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set_uint8(v___x_1170_, sizeof(void*)*1, v___x_1169_);
v___y_1144_ = v___x_1170_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1171_; 
lean_dec(v_n_1140_);
v___x_1171_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___y_1144_ = v___x_1171_;
goto v___jp_1143_;
}
v___jp_1143_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1142_);
lean_ctor_set(v___x_1145_, 1, v___y_1144_);
v___x_1146_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_1147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1149_ = l_Nat_reprFast(v_x_1139_);
v___x_1150_ = lean_string_append(v___x_1148_, v___x_1149_);
lean_dec_ref(v___x_1149_);
v___x_1151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1147_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_box(1);
v___x_1156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_1141_);
v___x_1158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
return v___x_1158_;
}
}
case 8:
{
lean_object* v_x_1172_; lean_object* v_b_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1191_; 
v_x_1172_ = lean_ctor_get(v_a_948_, 0);
v_b_1173_ = lean_ctor_get(v_a_948_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_a_948_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1175_ = v_a_948_;
v_isShared_1176_ = v_isSharedCheck_1191_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_b_1173_);
lean_inc(v_x_1172_);
lean_dec(v_a_948_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1191_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1177_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__27));
v___x_1178_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1179_ = l_Nat_reprFast(v_x_1172_);
v___x_1180_ = lean_string_append(v___x_1178_, v___x_1179_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 5);
lean_ctor_set(v___x_1175_, 1, v___x_1181_);
lean_ctor_set(v___x_1175_, 0, v___x_1177_);
v___x_1183_ = v___x_1175_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_box(1);
v___x_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_947_, v_b_1173_);
v___x_1189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
return v___x_1189_;
}
}
}
case 9:
{
lean_object* v_x_1192_; lean_object* v_xType_1193_; lean_object* v_cs_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_x_1192_ = lean_ctor_get(v_a_948_, 1);
lean_inc(v_x_1192_);
v_xType_1193_ = lean_ctor_get(v_a_948_, 2);
lean_inc(v_xType_1193_);
v_cs_1194_ = lean_ctor_get(v_a_948_, 3);
lean_inc_ref(v_cs_1194_);
lean_dec_ref_known(v_a_948_, 4);
v___x_1195_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__29));
v___x_1196_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1197_ = l_Nat_reprFast(v_x_1192_);
v___x_1198_ = lean_string_append(v___x_1196_, v___x_1197_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1195_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_xType_1193_);
v___x_1204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5));
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_get_size(v_cs_1194_);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec_ref(v_cs_1194_);
lean_dec(v_indent_947_);
v___x_1211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1206_);
lean_ctor_set(v___x_1211_, 1, v___x_1207_);
return v___x_1211_;
}
else
{
size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = lean_usize_of_nat(v___x_1209_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_947_, v_cs_1194_, v___x_1212_, v___x_1213_, v___x_1207_);
lean_dec_ref(v_cs_1194_);
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1206_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
return v___x_1215_;
}
}
case 10:
{
lean_object* v_x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v_indent_947_);
v_x_1216_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_x_1216_);
lean_dec_ref_known(v_a_948_, 1);
v___x_1217_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__33));
v___x_1218_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_1216_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
case 11:
{
lean_object* v_j_1220_; lean_object* v_ys_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_indent_947_);
v_j_1220_ = lean_ctor_get(v_a_948_, 0);
v_ys_1221_ = lean_ctor_get(v_a_948_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_a_948_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1223_ = v_a_948_;
v_isShared_1224_ = v_isSharedCheck_1235_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_ys_1221_);
lean_inc(v_j_1220_);
lean_dec(v_a_948_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1235_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1225_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__35));
v___x_1226_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_1227_ = l_Nat_reprFast(v_j_1220_);
v___x_1228_ = lean_string_append(v___x_1226_, v___x_1227_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 5);
lean_ctor_set(v___x_1223_, 1, v___x_1229_);
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1231_ = v___x_1223_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1221_);
lean_dec_ref(v_ys_1221_);
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
return v___x_1233_;
}
}
}
default: 
{
lean_object* v___x_1236_; 
lean_dec(v_indent_947_);
v___x_1236_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__37));
return v___x_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(lean_object* v_indent_1237_, lean_object* v_as_1238_, size_t v_i_1239_, size_t v_stop_1240_, lean_object* v_b_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_usize_dec_eq(v_i_1239_, v_stop_1240_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; 
v___x_1243_ = lean_array_uget_borrowed(v_as_1238_, v_i_1239_);
v___x_1244_ = lean_box(1);
v___x_1245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1245_, 0, v_b_1241_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
lean_inc_n(v_indent_1237_, 2);
v___x_1246_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop), 2, 1);
lean_closure_set(v___x_1246_, 0, v_indent_1237_);
lean_inc(v___x_1243_);
v___x_1247_ = l_Lean_IR_formatAlt(v___x_1246_, v_indent_1237_, v___x_1243_);
v___x_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1245_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_add(v_i_1239_, v___x_1249_);
v_i_1239_ = v___x_1250_;
v_b_1241_ = v___x_1248_;
goto _start;
}
else
{
lean_dec(v_indent_1237_);
return v_b_1241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0___boxed(lean_object* v_indent_1252_, lean_object* v_as_1253_, lean_object* v_i_1254_, lean_object* v_stop_1255_, lean_object* v_b_1256_){
_start:
{
size_t v_i_boxed_1257_; size_t v_stop_boxed_1258_; lean_object* v_res_1259_; 
v_i_boxed_1257_ = lean_unbox_usize(v_i_1254_);
lean_dec(v_i_1254_);
v_stop_boxed_1258_ = lean_unbox_usize(v_stop_1255_);
lean_dec(v_stop_1255_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_1252_, v_as_1253_, v_i_boxed_1257_, v_stop_boxed_1258_, v_b_1256_);
lean_dec_ref(v_as_1253_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody(lean_object* v_fnBody_1260_, lean_object* v_indent_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_1261_, v_fnBody_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatFnBody___lam__0(lean_object* v_fnBody_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_unsigned_to_nat(2u);
v___x_1265_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_1264_, v_fnBody_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringFnBody___lam__0(lean_object* v_b_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1269_ = lean_unsigned_to_nat(2u);
v___x_1270_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_1269_, v_b_1268_);
v___x_1271_ = l_Std_Format_defWidth;
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = l_Std_Format_pretty(v___x_1270_, v___x_1271_, v___x_1272_, v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatDecl(lean_object* v_decl_1282_, lean_object* v_indent_1283_){
_start:
{
if (lean_obj_tag(v_decl_1282_) == 0)
{
lean_object* v_f_1284_; lean_object* v_xs_1285_; lean_object* v_type_1286_; lean_object* v_body_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_f_1284_ = lean_ctor_get(v_decl_1282_, 0);
lean_inc(v_f_1284_);
v_xs_1285_ = lean_ctor_get(v_decl_1282_, 1);
lean_inc_ref(v_xs_1285_);
v_type_1286_ = lean_ctor_get(v_decl_1282_, 2);
lean_inc(v_type_1286_);
v_body_1287_ = lean_ctor_get(v_decl_1282_, 3);
lean_inc(v_body_1287_);
lean_dec_ref_known(v_decl_1282_, 5);
v___x_1288_ = ((lean_object*)(l_Lean_IR_formatDecl___closed__1));
v___x_1289_ = 1;
v___x_1290_ = l_Lean_Name_toString(v_f_1284_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1288_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_1285_);
lean_dec_ref(v_xs_1285_);
v___x_1294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_1286_);
v___x_1298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
lean_inc(v_indent_1283_);
v___x_1301_ = lean_nat_to_int(v_indent_1283_);
v___x_1302_ = lean_box(1);
v___x_1303_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_1283_, v_body_1287_);
v___x_1304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1301_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1300_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
return v___x_1306_;
}
else
{
lean_object* v_f_1307_; lean_object* v_xs_1308_; lean_object* v_type_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec(v_indent_1283_);
v_f_1307_ = lean_ctor_get(v_decl_1282_, 0);
lean_inc(v_f_1307_);
v_xs_1308_ = lean_ctor_get(v_decl_1282_, 1);
lean_inc_ref(v_xs_1308_);
v_type_1309_ = lean_ctor_get(v_decl_1282_, 2);
lean_inc(v_type_1309_);
lean_dec_ref_known(v_decl_1282_, 4);
v___x_1310_ = ((lean_object*)(l_Lean_IR_formatDecl___closed__3));
v___x_1311_ = 1;
v___x_1312_ = l_Lean_Name_toString(v_f_1307_, v___x_1311_);
v___x_1313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
v___x_1314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1310_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_1308_);
lean_dec_ref(v_xs_1308_);
v___x_1316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_1309_);
v___x_1320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatDecl___lam__0(lean_object* v_decl_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_unsigned_to_nat(2u);
v___x_1323_ = l_Lean_IR_formatDecl(v_decl_1321_, v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declToString(lean_object* v_d_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1327_ = lean_unsigned_to_nat(2u);
v___x_1328_ = l_Lean_IR_formatDecl(v_d_1326_, v___x_1327_);
v___x_1329_ = l_Std_Format_defWidth;
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = l_Std_Format_pretty(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1330_);
return v___x_1331_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Format(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_Format(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_Format(builtin);
}
#ifdef __cplusplus
}
#endif
