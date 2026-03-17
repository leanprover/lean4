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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v___f_58_; uint8_t v___x_59_; 
v___f_58_ = lean_alloc_closure((void*)(l_Lean_IR_formatArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_58_, 0, v_inst_51_);
v___x_59_ = lean_nat_dec_le(v___x_55_, v___x_55_);
if (v___x_59_ == 0)
{
if (v___x_57_ == 0)
{
lean_dec_ref(v___f_58_);
lean_dec_ref(v_args_52_);
return v___x_53_;
}
else
{
size_t v___x_60_; size_t v___x_61_; lean_object* v___x_62_; 
v___x_60_ = ((size_t)0ULL);
v___x_61_ = lean_usize_of_nat(v___x_55_);
v___x_62_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_56_, v___f_58_, v_args_52_, v___x_60_, v___x_61_, v___x_53_);
return v___x_62_;
}
}
else
{
size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; 
v___x_63_ = ((size_t)0ULL);
v___x_64_ = lean_usize_of_nat(v___x_55_);
v___x_65_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_56_, v___f_58_, v_args_52_, v___x_63_, v___x_64_, v___x_53_);
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray(lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_args_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_IR_formatArray___redArg(v_inst_67_, v_args_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(lean_object* v_x_70_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v_v_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_79_; 
v_v_71_ = lean_ctor_get(v_x_70_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_79_ == 0)
{
v___x_73_ = v_x_70_;
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_v_71_);
lean_dec(v_x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = l_Nat_reprFast(v_v_71_);
if (v_isShared_74_ == 0)
{
lean_ctor_set_tag(v___x_73_, 3);
lean_ctor_set(v___x_73_, 0, v___x_75_);
v___x_77_ = v___x_73_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
else
{
lean_object* v_v_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_88_; 
v_v_80_ = lean_ctor_get(v_x_70_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_88_ == 0)
{
v___x_82_ = v_x_70_;
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_v_80_);
lean_dec(v_x_70_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_84_ = l_String_quote(v_v_80_);
if (v_isShared_83_ == 0)
{
lean_ctor_set_tag(v___x_82_, 3);
lean_ctor_set(v___x_82_, 0, v___x_84_);
v___x_86_ = v___x_82_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatLitVal___private__1(lean_object* v_a_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(v_a_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(lean_object* v_x_105_){
_start:
{
lean_object* v_name_106_; lean_object* v_cidx_107_; lean_object* v_usize_108_; lean_object* v_ssize_109_; lean_object* v_r_111_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_r_125_; uint8_t v___y_127_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_name_106_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_name_106_);
v_cidx_107_ = lean_ctor_get(v_x_105_, 1);
lean_inc(v_cidx_107_);
v_usize_108_ = lean_ctor_get(v_x_105_, 3);
lean_inc(v_usize_108_);
v_ssize_109_ = lean_ctor_get(v_x_105_, 4);
lean_inc(v_ssize_109_);
lean_dec_ref(v_x_105_);
v___x_122_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5));
v___x_123_ = l_Nat_reprFast(v_cidx_107_);
v___x_124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
v_r_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_125_, 0, v___x_122_);
lean_ctor_set(v_r_125_, 1, v___x_124_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_nat_dec_lt(v___x_137_, v_usize_108_);
if (v___x_138_ == 0)
{
uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_lt(v___x_137_, v_ssize_109_);
v___y_127_ = v___x_139_;
goto v___jp_126_;
}
else
{
v___y_127_ = v___x_138_;
goto v___jp_126_;
}
v___jp_110_:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_box(0);
v___x_113_ = lean_name_eq(v_name_106_, v___x_112_);
if (v___x_113_ == 0)
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_r_121_; 
v___x_114_ = 1;
v___x_115_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_116_, 0, v_r_111_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = l_Lean_Name_toString(v_name_106_, v___x_114_);
v___x_118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v_r_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_121_, 0, v___x_119_);
lean_ctor_set(v_r_121_, 1, v___x_120_);
return v_r_121_;
}
else
{
lean_dec(v_name_106_);
return v_r_111_;
}
}
v___jp_126_:
{
if (v___y_127_ == 0)
{
lean_dec(v_ssize_109_);
lean_dec(v_usize_108_);
v_r_111_ = v_r_125_;
goto v___jp_110_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_r_136_; 
v___x_128_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7));
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v_r_125_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Nat_reprFast(v_usize_108_);
v___x_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_129_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_128_);
v___x_134_ = l_Nat_reprFast(v_ssize_109_);
v___x_135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
v_r_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_136_, 0, v___x_133_);
lean_ctor_set(v_r_136_, 1, v___x_135_);
v_r_111_ = v_r_136_;
goto v___jp_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatCtorInfo___private__1(lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_a_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(lean_object* v_as_144_, size_t v_i_145_, size_t v_stop_146_, lean_object* v_b_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_usize_dec_eq(v_i_145_, v_stop_146_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; size_t v___x_154_; size_t v___x_155_; 
v___x_149_ = lean_array_uget_borrowed(v_as_144_, v_i_145_);
v___x_150_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_151_, 0, v_b_147_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
lean_inc(v___x_149_);
v___x_152_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v___x_149_);
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_add(v_i_145_, v___x_154_);
v_i_145_ = v___x_155_;
v_b_147_ = v___x_153_;
goto _start;
}
else
{
return v_b_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0___boxed(lean_object* v_as_157_, lean_object* v_i_158_, lean_object* v_stop_159_, lean_object* v_b_160_){
_start:
{
size_t v_i_boxed_161_; size_t v_stop_boxed_162_; lean_object* v_res_163_; 
v_i_boxed_161_ = lean_unbox_usize(v_i_158_);
lean_dec(v_i_158_);
v_stop_boxed_162_ = lean_unbox_usize(v_stop_159_);
lean_dec(v_stop_159_);
v_res_163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_as_157_, v_i_boxed_161_, v_stop_boxed_162_, v_b_160_);
lean_dec_ref(v_as_157_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(lean_object* v_args_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_array_get_size(v_args_164_);
v___x_168_ = lean_nat_dec_lt(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
return v___x_165_;
}
else
{
uint8_t v___x_169_; 
v___x_169_ = lean_nat_dec_le(v___x_167_, v___x_167_);
if (v___x_169_ == 0)
{
if (v___x_168_ == 0)
{
return v___x_165_;
}
else
{
size_t v___x_170_; size_t v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((size_t)0ULL);
v___x_171_ = lean_usize_of_nat(v___x_167_);
v___x_172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_164_, v___x_170_, v___x_171_, v___x_165_);
return v___x_172_;
}
}
else
{
size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; 
v___x_173_ = ((size_t)0ULL);
v___x_174_ = lean_usize_of_nat(v___x_167_);
v___x_175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_164_, v___x_173_, v___x_174_, v___x_165_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(lean_object* v_args_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_args_176_);
lean_dec_ref(v_args_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(lean_object* v_x_219_){
_start:
{
switch(lean_obj_tag(v_x_219_))
{
case 0:
{
lean_object* v_i_220_; lean_object* v_ys_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_230_; 
v_i_220_ = lean_ctor_get(v_x_219_, 0);
v_ys_221_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_230_ == 0)
{
v___x_223_ = v_x_219_;
v_isShared_224_ = v_isSharedCheck_230_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_ys_221_);
lean_inc(v_i_220_);
lean_dec(v_x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_230_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_220_);
v___x_226_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_221_);
lean_dec_ref(v_ys_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set_tag(v___x_223_, 5);
lean_ctor_set(v___x_223_, 1, v___x_226_);
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
case 1:
{
lean_object* v_n_231_; lean_object* v_x_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_249_; 
v_n_231_ = lean_ctor_get(v_x_219_, 0);
v_x_232_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_249_ == 0)
{
v___x_234_ = v_x_219_;
v_isShared_235_ = v_isSharedCheck_249_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_x_232_);
lean_inc(v_n_231_);
lean_dec(v_x_219_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_249_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_236_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1));
v___x_237_ = l_Nat_reprFast(v_n_231_);
v___x_238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
if (v_isShared_235_ == 0)
{
lean_ctor_set_tag(v___x_234_, 5);
lean_ctor_set(v___x_234_, 1, v___x_238_);
lean_ctor_set(v___x_234_, 0, v___x_236_);
v___x_240_ = v___x_234_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_248_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_241_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_244_ = l_Nat_reprFast(v_x_232_);
v___x_245_ = lean_string_append(v___x_243_, v___x_244_);
lean_dec_ref(v___x_244_);
v___x_246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_242_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
return v___x_247_;
}
}
}
case 2:
{
lean_object* v_x_250_; lean_object* v_i_251_; uint8_t v_updtHeader_252_; lean_object* v_ys_253_; lean_object* v___x_254_; lean_object* v___y_256_; 
v_x_250_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_x_250_);
v_i_251_ = lean_ctor_get(v_x_219_, 1);
lean_inc_ref(v_i_251_);
v_updtHeader_252_ = lean_ctor_get_uint8(v_x_219_, sizeof(void*)*3);
v_ys_253_ = lean_ctor_get(v_x_219_, 2);
lean_inc_ref(v_ys_253_);
lean_dec_ref(v_x_219_);
v___x_254_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5));
if (v_updtHeader_252_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8));
v___y_256_ = v___x_272_;
goto v___jp_255_;
}
else
{
lean_object* v___x_273_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9));
v___y_256_ = v___x_273_;
goto v___jp_255_;
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_257_, 0, v___y_256_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_254_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_262_ = l_Nat_reprFast(v_x_250_);
v___x_263_ = lean_string_append(v___x_261_, v___x_262_);
lean_dec_ref(v___x_262_);
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
v___x_265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_260_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7));
v___x_267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_251_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_253_);
lean_dec_ref(v_ys_253_);
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
return v___x_271_;
}
}
case 3:
{
lean_object* v_i_274_; lean_object* v_x_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_292_; 
v_i_274_ = lean_ctor_get(v_x_219_, 0);
v_x_275_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_292_ == 0)
{
v___x_277_ = v_x_219_;
v_isShared_278_ = v_isSharedCheck_292_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_x_275_);
lean_inc(v_i_274_);
lean_dec(v_x_219_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_292_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11));
v___x_280_ = l_Nat_reprFast(v_i_274_);
v___x_281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
if (v_isShared_278_ == 0)
{
lean_ctor_set_tag(v___x_277_, 5);
lean_ctor_set(v___x_277_, 1, v___x_281_);
lean_ctor_set(v___x_277_, 0, v___x_279_);
v___x_283_ = v___x_277_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_281_);
v___x_283_ = v_reuseFailAlloc_291_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_287_ = l_Nat_reprFast(v_x_275_);
v___x_288_ = lean_string_append(v___x_286_, v___x_287_);
lean_dec_ref(v___x_287_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_285_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
return v___x_290_;
}
}
}
case 4:
{
lean_object* v_i_293_; lean_object* v_x_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_311_; 
v_i_293_ = lean_ctor_get(v_x_219_, 0);
v_x_294_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_311_ == 0)
{
v___x_296_ = v_x_219_;
v_isShared_297_ = v_isSharedCheck_311_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_x_294_);
lean_inc(v_i_293_);
lean_dec(v_x_219_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_311_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_298_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13));
v___x_299_ = l_Nat_reprFast(v_i_293_);
v___x_300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 5);
lean_ctor_set(v___x_296_, 1, v___x_300_);
lean_ctor_set(v___x_296_, 0, v___x_298_);
v___x_302_ = v___x_296_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_310_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_303_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_306_ = l_Nat_reprFast(v_x_294_);
v___x_307_ = lean_string_append(v___x_305_, v___x_306_);
lean_dec_ref(v___x_306_);
v___x_308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_304_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
return v___x_309_;
}
}
}
case 5:
{
lean_object* v_n_312_; lean_object* v_offset_313_; lean_object* v_x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_n_312_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_n_312_);
v_offset_313_ = lean_ctor_get(v_x_219_, 1);
lean_inc(v_offset_313_);
v_x_314_ = lean_ctor_get(v_x_219_, 2);
lean_inc(v_x_314_);
lean_dec_ref(v_x_219_);
v___x_315_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15));
v___x_316_ = l_Nat_reprFast(v_n_312_);
v___x_317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_315_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = l_Nat_reprFast(v_offset_313_);
v___x_322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_327_ = l_Nat_reprFast(v_x_314_);
v___x_328_ = lean_string_append(v___x_326_, v___x_327_);
lean_dec_ref(v___x_327_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_325_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
return v___x_330_;
}
case 6:
{
lean_object* v_c_331_; lean_object* v_ys_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_343_; 
v_c_331_ = lean_ctor_get(v_x_219_, 0);
v_ys_332_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_343_ == 0)
{
v___x_334_ = v_x_219_;
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_ys_332_);
lean_inc(v_c_331_);
lean_dec(v_x_219_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_336_ = 1;
v___x_337_ = l_Lean_Name_toString(v_c_331_, v___x_336_);
v___x_338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
v___x_339_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_332_);
lean_dec_ref(v_ys_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set_tag(v___x_334_, 5);
lean_ctor_set(v___x_334_, 1, v___x_339_);
lean_ctor_set(v___x_334_, 0, v___x_338_);
v___x_341_ = v___x_334_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
case 7:
{
lean_object* v_c_344_; lean_object* v_ys_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_358_; 
v_c_344_ = lean_ctor_get(v_x_219_, 0);
v_ys_345_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_358_ == 0)
{
v___x_347_ = v_x_219_;
v_isShared_348_ = v_isSharedCheck_358_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_ys_345_);
lean_inc(v_c_344_);
lean_dec(v_x_219_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_358_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19));
v___x_350_ = 1;
v___x_351_ = l_Lean_Name_toString(v_c_344_, v___x_350_);
v___x_352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 5);
lean_ctor_set(v___x_347_, 1, v___x_352_);
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_354_ = v___x_347_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_352_);
v___x_354_ = v_reuseFailAlloc_357_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_345_);
lean_dec_ref(v_ys_345_);
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
}
}
case 8:
{
lean_object* v_x_359_; lean_object* v_ys_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_374_; 
v_x_359_ = lean_ctor_get(v_x_219_, 0);
v_ys_360_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_374_ == 0)
{
v___x_362_ = v_x_219_;
v_isShared_363_ = v_isSharedCheck_374_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_ys_360_);
lean_inc(v_x_359_);
lean_dec(v_x_219_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_374_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21));
v___x_365_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_366_ = l_Nat_reprFast(v_x_359_);
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
lean_dec_ref(v___x_366_);
v___x_368_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 5);
lean_ctor_set(v___x_362_, 1, v___x_368_);
lean_ctor_set(v___x_362_, 0, v___x_364_);
v___x_370_ = v___x_362_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_368_);
v___x_370_ = v_reuseFailAlloc_373_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_360_);
lean_dec_ref(v_ys_360_);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
}
case 9:
{
lean_object* v_x_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v_x_375_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v_x_219_, 0);
lean_dec(v_unused_388_);
v___x_377_ = v_x_219_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_x_375_);
lean_dec(v_x_219_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23));
v___x_380_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_381_ = l_Nat_reprFast(v_x_375_);
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
lean_dec_ref(v___x_381_);
v___x_383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 5);
lean_ctor_set(v___x_377_, 1, v___x_383_);
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_385_ = v___x_377_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
case 10:
{
lean_object* v_x_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_401_; 
v_x_389_ = lean_ctor_get(v_x_219_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_401_ == 0)
{
v___x_391_ = v_x_219_;
v_isShared_392_ = v_isSharedCheck_401_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_x_389_);
lean_dec(v_x_219_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_401_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_393_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25));
v___x_394_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_395_ = l_Nat_reprFast(v_x_389_);
v___x_396_ = lean_string_append(v___x_394_, v___x_395_);
lean_dec_ref(v___x_395_);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 3);
lean_ctor_set(v___x_391_, 0, v___x_396_);
v___x_398_ = v___x_391_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_400_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_393_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
return v___x_399_;
}
}
}
case 11:
{
lean_object* v_v_402_; lean_object* v___x_403_; 
v_v_402_ = lean_ctor_get(v_x_219_, 0);
lean_inc_ref(v_v_402_);
lean_dec_ref(v_x_219_);
v___x_403_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(v_v_402_);
return v___x_403_;
}
default: 
{
lean_object* v_x_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
v_x_404_ = lean_ctor_get(v_x_219_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_416_ == 0)
{
v___x_406_ = v_x_219_;
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_x_404_);
lean_dec(v_x_219_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_408_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27));
v___x_409_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_410_ = l_Nat_reprFast(v_x_404_);
v___x_411_ = lean_string_append(v___x_409_, v___x_410_);
lean_dec_ref(v___x_410_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 3);
lean_ctor_set(v___x_406_, 0, v___x_411_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; 
v___x_414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_408_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
return v___x_414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatExpr___private__1(lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_a_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringExpr___lam__0(lean_object* v_e_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_422_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_421_);
v___x_423_ = l_Std_Format_defWidth;
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = l_Std_Format_pretty(v___x_422_, v___x_423_, v___x_424_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__1(lean_object* v_a_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_nat_to_int(v_a_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
lean_object* v___x_462_; 
lean_dec(v_x_461_);
v___x_462_ = lean_box(0);
return v___x_462_;
}
else
{
lean_object* v_tail_463_; 
v_tail_463_ = lean_ctor_get(v_x_460_, 1);
if (lean_obj_tag(v_tail_463_) == 0)
{
lean_object* v_head_464_; lean_object* v___x_465_; 
lean_dec(v_x_461_);
v_head_464_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_head_464_);
lean_dec_ref(v_x_460_);
v___x_465_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_464_);
return v___x_465_;
}
else
{
lean_object* v_head_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc(v_tail_463_);
v_head_466_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_head_466_);
lean_dec_ref(v_x_460_);
v___x_467_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_466_);
v___x_468_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(v_x_461_, v___x_467_, v_tail_463_);
return v___x_468_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20));
v___x_471_ = lean_string_length(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22);
v___x_473_ = lean_nat_to_int(v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object* v_x_488_){
_start:
{
switch(lean_obj_tag(v_x_488_))
{
case 0:
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1));
return v___x_489_;
}
case 1:
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3));
return v___x_490_;
}
case 2:
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5));
return v___x_491_;
}
case 3:
{
lean_object* v___x_492_; 
v___x_492_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7));
return v___x_492_;
}
case 4:
{
lean_object* v___x_493_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9));
return v___x_493_;
}
case 5:
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11));
return v___x_494_;
}
case 6:
{
lean_object* v___x_495_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2));
return v___x_495_;
}
case 7:
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13));
return v___x_496_;
}
case 8:
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15));
return v___x_497_;
}
case 9:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17));
return v___x_498_;
}
case 10:
{
lean_object* v_types_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_518_; 
v_types_499_ = lean_ctor_get(v_x_488_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_x_488_, 0);
lean_dec(v_unused_519_);
v___x_501_ = v_x_488_;
v_isShared_502_ = v_isSharedCheck_518_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_types_499_);
lean_dec(v_x_488_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_518_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_503_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19));
v___x_504_ = lean_array_to_list(v_types_499_);
v___x_505_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_506_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_504_, v___x_505_);
v___x_507_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
v___x_508_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24));
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 5);
lean_ctor_set(v___x_501_, 1, v___x_506_);
lean_ctor_set(v___x_501_, 0, v___x_508_);
v___x_510_ = v___x_501_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_506_);
v___x_510_ = v_reuseFailAlloc_517_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25));
v___x_512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_507_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = 0;
v___x_515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_514_);
v___x_516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_503_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
}
}
case 11:
{
lean_object* v_types_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_539_; 
v_types_520_ = lean_ctor_get(v_x_488_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_x_488_, 0);
lean_dec(v_unused_540_);
v___x_522_ = v_x_488_;
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_types_520_);
lean_dec(v_x_488_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27));
v___x_525_ = lean_array_to_list(v_types_520_);
v___x_526_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_527_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_525_, v___x_526_);
v___x_528_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
v___x_529_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24));
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 5);
lean_ctor_set(v___x_522_, 1, v___x_527_);
lean_ctor_set(v___x_522_, 0, v___x_529_);
v___x_531_ = v___x_522_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_527_);
v___x_531_ = v_reuseFailAlloc_538_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25));
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_528_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = 0;
v___x_536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*1, v___x_535_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_524_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
return v___x_537_;
}
}
}
case 12:
{
lean_object* v___x_541_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29));
return v___x_541_;
}
default: 
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31));
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_dec(v_x_543_);
return v_x_544_;
}
else
{
lean_object* v_head_546_; lean_object* v_tail_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_557_; 
v_head_546_ = lean_ctor_get(v_x_545_, 0);
v_tail_547_ = lean_ctor_get(v_x_545_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_557_ == 0)
{
v___x_549_ = v_x_545_;
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_tail_547_);
lean_inc(v_head_546_);
lean_dec(v_x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
lean_inc(v_x_543_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 5);
lean_ctor_set(v___x_549_, 1, v_x_543_);
lean_ctor_set(v___x_549_, 0, v_x_544_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_x_544_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_x_543_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_546_);
v___x_554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v_x_544_ = v___x_554_;
v_x_545_ = v_tail_547_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatIRType___private__1(lean_object* v_a_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringIRType___lam__0(lean_object* v_f_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = l_Std_Format_defWidth;
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = l_Std_Format_pretty(v_f_562_, v___x_563_, v___x_564_, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(lean_object* v_x_581_){
_start:
{
lean_object* v_x_582_; uint8_t v_borrow_583_; lean_object* v_ty_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___y_594_; 
v_x_582_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_x_582_);
v_borrow_583_ = lean_ctor_get_uint8(v_x_581_, sizeof(void*)*2);
v_ty_584_ = lean_ctor_get(v_x_581_, 1);
lean_inc(v_ty_584_);
lean_dec_ref(v_x_581_);
v___x_585_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1));
v___x_586_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_587_ = l_Nat_reprFast(v_x_582_);
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
lean_dec_ref(v___x_587_);
v___x_589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_585_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
if (v_borrow_583_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8));
v___y_594_ = v___x_601_;
goto v___jp_593_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6));
v___y_594_ = v___x_602_;
goto v___jp_593_;
}
v___jp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_595_, 0, v___y_594_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_592_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_584_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5));
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatParam___private__1(lean_object* v_a_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v_a_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatAlt(lean_object* v_fmt_613_, lean_object* v_indent_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v_info_616_; lean_object* v_b_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_635_; 
v_info_616_ = lean_ctor_get(v_x_615_, 0);
v_b_617_ = lean_ctor_get(v_x_615_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_635_ == 0)
{
v___x_619_ = v_x_615_;
v_isShared_620_ = v_isSharedCheck_635_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_b_617_);
lean_inc(v_info_616_);
lean_dec(v_x_615_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_635_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_name_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v_name_621_ = lean_ctor_get(v_info_616_, 0);
lean_inc(v_name_621_);
lean_dec_ref(v_info_616_);
v___x_622_ = 1;
v___x_623_ = l_Lean_Name_toString(v_name_621_, v___x_622_);
v___x_624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
v___x_625_ = ((lean_object*)(l_Lean_IR_formatAlt___closed__1));
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 5);
lean_ctor_set(v___x_619_, 1, v___x_625_);
lean_ctor_set(v___x_619_, 0, v___x_624_);
v___x_627_ = v___x_619_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_634_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_628_ = lean_nat_to_int(v_indent_614_);
v___x_629_ = lean_box(1);
v___x_630_ = lean_apply_1(v_fmt_613_, v_b_617_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_628_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_627_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
}
}
else
{
lean_object* v_b_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_b_636_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_b_636_);
lean_dec_ref(v_x_615_);
v___x_637_ = ((lean_object*)(l_Lean_IR_formatAlt___closed__3));
v___x_638_ = lean_nat_to_int(v_indent_614_);
v___x_639_ = lean_box(1);
v___x_640_ = lean_apply_1(v_fmt_613_, v_b_636_);
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_638_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_637_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(lean_object* v_as_644_, size_t v_i_645_, size_t v_stop_646_, lean_object* v_b_647_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = lean_usize_dec_eq(v_i_645_, v_stop_646_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; size_t v___x_654_; size_t v___x_655_; 
v___x_649_ = lean_array_uget_borrowed(v_as_644_, v_i_645_);
v___x_650_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v_b_647_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
lean_inc(v___x_649_);
v___x_652_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v___x_649_);
v___x_653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_645_, v___x_654_);
v_i_645_ = v___x_655_;
v_b_647_ = v___x_653_;
goto _start;
}
else
{
return v_b_647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0___boxed(lean_object* v_as_657_, lean_object* v_i_658_, lean_object* v_stop_659_, lean_object* v_b_660_){
_start:
{
size_t v_i_boxed_661_; size_t v_stop_boxed_662_; lean_object* v_res_663_; 
v_i_boxed_661_ = lean_unbox_usize(v_i_658_);
lean_dec(v_i_658_);
v_stop_boxed_662_ = lean_unbox_usize(v_stop_659_);
lean_dec(v_stop_659_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_as_657_, v_i_boxed_661_, v_stop_boxed_662_, v_b_660_);
lean_dec_ref(v_as_657_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(lean_object* v_args_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_665_ = lean_box(0);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v_args_664_);
v___x_668_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
return v___x_665_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_le(v___x_667_, v___x_667_);
if (v___x_669_ == 0)
{
if (v___x_668_ == 0)
{
return v___x_665_;
}
else
{
size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((size_t)0ULL);
v___x_671_ = lean_usize_of_nat(v___x_667_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_664_, v___x_670_, v___x_671_, v___x_665_);
return v___x_672_;
}
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_667_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_664_, v___x_673_, v___x_674_, v___x_665_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0___boxed(lean_object* v_args_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_args_676_);
lean_dec_ref(v_args_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams(lean_object* v_ps_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_ps_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams___boxed(lean_object* v_ps_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_IR_formatParams(v_ps_680_);
lean_dec_ref(v_ps_680_);
return v_res_681_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__21(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0));
v___x_714_ = lean_string_length(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__22(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__21, &l_Lean_IR_formatFnBodyHead___closed__21_once, _init_l_Lean_IR_formatFnBodyHead___closed__21);
v___x_716_ = lean_nat_to_int(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBodyHead(lean_object* v_x_740_){
_start:
{
switch(lean_obj_tag(v_x_740_))
{
case 0:
{
lean_object* v_x_741_; lean_object* v_ty_742_; lean_object* v_e_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_x_741_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_x_741_);
v_ty_742_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_ty_742_);
v_e_743_ = lean_ctor_get(v_x_740_, 2);
lean_inc_ref(v_e_743_);
lean_dec_ref(v_x_740_);
v___x_744_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__1));
v___x_745_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_746_ = l_Nat_reprFast(v_x_741_);
v___x_747_ = lean_string_append(v___x_745_, v___x_746_);
lean_dec_ref(v___x_746_);
v___x_748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
v___x_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_744_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_742_);
v___x_753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_743_);
v___x_757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
return v___x_757_;
}
case 1:
{
lean_object* v_j_758_; lean_object* v_xs_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_j_758_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_j_758_);
v_xs_759_ = lean_ctor_get(v_x_740_, 1);
lean_inc_ref(v_xs_759_);
lean_dec_ref(v_x_740_);
v___x_760_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_761_ = l_Nat_reprFast(v_j_758_);
v___x_762_ = lean_string_append(v___x_760_, v___x_761_);
lean_dec_ref(v___x_761_);
v___x_763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
v___x_764_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_759_);
lean_dec_ref(v_xs_759_);
v___x_765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
return v___x_767_;
}
case 2:
{
lean_object* v_x_768_; lean_object* v_i_769_; lean_object* v_y_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_x_768_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_x_768_);
v_i_769_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_i_769_);
v_y_770_ = lean_ctor_get(v_x_740_, 2);
lean_inc(v_y_770_);
lean_dec_ref(v_x_740_);
v___x_771_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__8));
v___x_772_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_773_ = l_Nat_reprFast(v_x_768_);
v___x_774_ = lean_string_append(v___x_772_, v___x_773_);
lean_dec_ref(v___x_773_);
v___x_775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
v___x_776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_771_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Nat_reprFast(v_i_769_);
v___x_780_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___x_781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_778_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_770_);
v___x_785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
return v___x_785_;
}
case 3:
{
lean_object* v_x_786_; lean_object* v_cidx_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_x_786_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_x_786_);
v_cidx_787_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_cidx_787_);
lean_dec_ref(v_x_740_);
v___x_788_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__12));
v___x_789_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_790_ = l_Nat_reprFast(v_x_786_);
v___x_791_ = lean_string_append(v___x_789_, v___x_790_);
lean_dec_ref(v___x_790_);
v___x_792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
v___x_793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_788_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Nat_reprFast(v_cidx_787_);
v___x_797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
v___x_798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_795_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
return v___x_798_;
}
case 4:
{
lean_object* v_x_799_; lean_object* v_i_800_; lean_object* v_y_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_x_799_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_x_799_);
v_i_800_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_i_800_);
v_y_801_ = lean_ctor_get(v_x_740_, 2);
lean_inc(v_y_801_);
lean_dec_ref(v_x_740_);
v___x_802_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_803_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_804_ = l_Nat_reprFast(v_x_799_);
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
lean_dec_ref(v___x_804_);
v___x_806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
v___x_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_802_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Nat_reprFast(v_i_800_);
v___x_811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_809_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Nat_reprFast(v_y_801_);
v___x_816_ = lean_string_append(v___x_803_, v___x_815_);
lean_dec_ref(v___x_815_);
v___x_817_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
v___x_818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_814_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
return v___x_818_;
}
case 5:
{
lean_object* v_x_819_; lean_object* v_i_820_; lean_object* v_offset_821_; lean_object* v_y_822_; lean_object* v_ty_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_x_819_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_x_819_);
v_i_820_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_i_820_);
v_offset_821_ = lean_ctor_get(v_x_740_, 2);
lean_inc(v_offset_821_);
v_y_822_ = lean_ctor_get(v_x_740_, 3);
lean_inc(v_y_822_);
v_ty_823_ = lean_ctor_get(v_x_740_, 4);
lean_inc(v_ty_823_);
lean_dec_ref(v_x_740_);
v___x_824_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__16));
v___x_825_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_826_ = l_Nat_reprFast(v_x_819_);
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
lean_dec_ref(v___x_826_);
v___x_828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_824_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Nat_reprFast(v_i_820_);
v___x_833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_831_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = l_Nat_reprFast(v_offset_821_);
v___x_838_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_836_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__18));
v___x_841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_823_);
v___x_843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Nat_reprFast(v_y_822_);
v___x_847_ = lean_string_append(v___x_825_, v___x_846_);
lean_dec_ref(v___x_846_);
v___x_848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
v___x_849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_845_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
return v___x_849_;
}
case 6:
{
lean_object* v_x_850_; lean_object* v_n_851_; lean_object* v___x_852_; lean_object* v___y_854_; lean_object* v___x_863_; uint8_t v___x_864_; 
v_x_850_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_x_850_);
v_n_851_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_n_851_);
lean_dec_ref(v_x_740_);
v___x_852_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__20));
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_dec_eq(v_n_851_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; 
v___x_865_ = l_Nat_reprFast(v_n_851_);
v___x_866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__22, &l_Lean_IR_formatFnBodyHead___closed__22_once, _init_l_Lean_IR_formatFnBodyHead___closed__22);
v___x_868_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_866_);
v___x_870_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_867_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = 0;
v___x_874_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*1, v___x_873_);
v___y_854_ = v___x_874_;
goto v___jp_853_;
}
else
{
lean_object* v___x_875_; 
lean_dec(v_n_851_);
v___x_875_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___y_854_ = v___x_875_;
goto v___jp_853_;
}
v___jp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_852_);
lean_ctor_set(v___x_855_, 1, v___y_854_);
v___x_856_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_859_ = l_Nat_reprFast(v_x_850_);
v___x_860_ = lean_string_append(v___x_858_, v___x_859_);
lean_dec_ref(v___x_859_);
v___x_861_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_857_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
return v___x_862_;
}
}
case 7:
{
lean_object* v_x_876_; lean_object* v_n_877_; lean_object* v___x_878_; lean_object* v___y_880_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_x_876_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_x_876_);
v_n_877_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_n_877_);
lean_dec_ref(v_x_740_);
v___x_878_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__25));
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_nat_dec_eq(v_n_877_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; 
v___x_891_ = l_Nat_reprFast(v_n_877_);
v___x_892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
v___x_893_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__22, &l_Lean_IR_formatFnBodyHead___closed__22_once, _init_l_Lean_IR_formatFnBodyHead___closed__22);
v___x_894_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_892_);
v___x_896_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_893_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = 0;
v___x_900_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set_uint8(v___x_900_, sizeof(void*)*1, v___x_899_);
v___y_880_ = v___x_900_;
goto v___jp_879_;
}
else
{
lean_object* v___x_901_; 
lean_dec(v_n_877_);
v___x_901_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___y_880_ = v___x_901_;
goto v___jp_879_;
}
v___jp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_878_);
lean_ctor_set(v___x_881_, 1, v___y_880_);
v___x_882_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_885_ = l_Nat_reprFast(v_x_876_);
v___x_886_ = lean_string_append(v___x_884_, v___x_885_);
lean_dec_ref(v___x_885_);
v___x_887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_883_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
return v___x_888_;
}
}
case 8:
{
lean_object* v_x_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_914_; 
v_x_902_ = lean_ctor_get(v_x_740_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_x_740_, 1);
lean_dec(v_unused_915_);
v___x_904_ = v_x_740_;
v_isShared_905_ = v_isSharedCheck_914_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_x_902_);
lean_dec(v_x_740_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_914_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_906_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__27));
v___x_907_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_908_ = l_Nat_reprFast(v_x_902_);
v___x_909_ = lean_string_append(v___x_907_, v___x_908_);
lean_dec_ref(v___x_908_);
v___x_910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 5);
lean_ctor_set(v___x_904_, 1, v___x_910_);
lean_ctor_set(v___x_904_, 0, v___x_906_);
v___x_912_ = v___x_904_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
case 9:
{
lean_object* v_x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_x_916_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_x_916_);
lean_dec_ref(v_x_740_);
v___x_917_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__29));
v___x_918_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_919_ = l_Nat_reprFast(v_x_916_);
v___x_920_ = lean_string_append(v___x_918_, v___x_919_);
lean_dec_ref(v___x_919_);
v___x_921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_917_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__31));
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
return v___x_924_;
}
case 10:
{
lean_object* v_x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_x_925_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_x_925_);
lean_dec_ref(v_x_740_);
v___x_926_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__33));
v___x_927_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_925_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
return v___x_928_;
}
case 11:
{
lean_object* v_j_929_; lean_object* v_ys_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_944_; 
v_j_929_ = lean_ctor_get(v_x_740_, 0);
v_ys_930_ = lean_ctor_get(v_x_740_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_944_ == 0)
{
v___x_932_ = v_x_740_;
v_isShared_933_ = v_isSharedCheck_944_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_ys_930_);
lean_inc(v_j_929_);
lean_dec(v_x_740_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_944_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_934_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__35));
v___x_935_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_936_ = l_Nat_reprFast(v_j_929_);
v___x_937_ = lean_string_append(v___x_935_, v___x_936_);
lean_dec_ref(v___x_936_);
v___x_938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 5);
lean_ctor_set(v___x_932_, 1, v___x_938_);
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_940_ = v___x_932_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_943_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_930_);
lean_dec_ref(v_ys_930_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
return v___x_942_;
}
}
}
default: 
{
lean_object* v___x_945_; 
v___x_945_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__37));
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_format_fn_body_head(lean_object* v_fn_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_947_ = l_Lean_IR_formatFnBodyHead(v_fn_946_);
v___x_948_ = l_Std_Format_defWidth;
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = l_Std_Format_pretty(v___x_947_, v___x_948_, v___x_949_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(lean_object* v_indent_960_, lean_object* v_a_961_){
_start:
{
switch(lean_obj_tag(v_a_961_))
{
case 0:
{
lean_object* v_x_962_; lean_object* v_ty_963_; lean_object* v_e_964_; lean_object* v_b_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_x_962_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_x_962_);
v_ty_963_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_ty_963_);
v_e_964_ = lean_ctor_get(v_a_961_, 2);
lean_inc_ref(v_e_964_);
v_b_965_ = lean_ctor_get(v_a_961_, 3);
lean_inc(v_b_965_);
lean_dec_ref(v_a_961_);
v___x_966_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__1));
v___x_967_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_968_ = l_Nat_reprFast(v_x_962_);
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
lean_dec_ref(v___x_968_);
v___x_970_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_966_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_963_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_964_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_box(1);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_965_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
return v___x_985_;
}
case 1:
{
lean_object* v_j_986_; lean_object* v_xs_987_; lean_object* v_v_988_; lean_object* v_b_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_j_986_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_j_986_);
v_xs_987_ = lean_ctor_get(v_a_961_, 1);
lean_inc_ref(v_xs_987_);
v_v_988_ = lean_ctor_get(v_a_961_, 2);
lean_inc(v_v_988_);
v_b_989_ = lean_ctor_get(v_a_961_, 3);
lean_inc(v_b_989_);
lean_dec_ref(v_a_961_);
v___x_990_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_991_ = l_Nat_reprFast(v_j_986_);
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
lean_dec_ref(v___x_991_);
v___x_993_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
v___x_994_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_987_);
lean_dec_ref(v_xs_987_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_inc(v_indent_960_);
v___x_998_ = lean_nat_to_int(v_indent_960_);
v___x_999_ = lean_box(1);
lean_inc(v_indent_960_);
v___x_1000_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_v_988_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_998_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_997_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_999_);
v___x_1007_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_989_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
return v___x_1008_;
}
case 2:
{
lean_object* v_x_1009_; lean_object* v_i_1010_; lean_object* v_y_1011_; lean_object* v_b_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_x_1009_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_x_1009_);
v_i_1010_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_i_1010_);
v_y_1011_ = lean_ctor_get(v_a_961_, 2);
lean_inc(v_y_1011_);
v_b_1012_ = lean_ctor_get(v_a_961_, 3);
lean_inc(v_b_1012_);
lean_dec_ref(v_a_961_);
v___x_1013_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__8));
v___x_1014_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1015_ = l_Nat_reprFast(v_x_1009_);
v___x_1016_ = lean_string_append(v___x_1014_, v___x_1015_);
lean_dec_ref(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1013_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Nat_reprFast(v_i_1010_);
v___x_1022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1020_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_1011_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_box(1);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_1012_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
return v___x_1033_;
}
case 3:
{
lean_object* v_x_1034_; lean_object* v_cidx_1035_; lean_object* v_b_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_x_1034_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_x_1034_);
v_cidx_1035_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_cidx_1035_);
v_b_1036_ = lean_ctor_get(v_a_961_, 2);
lean_inc(v_b_1036_);
lean_dec_ref(v_a_961_);
v___x_1037_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__12));
v___x_1038_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1039_ = l_Nat_reprFast(v_x_1034_);
v___x_1040_ = lean_string_append(v___x_1038_, v___x_1039_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1037_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = l_Nat_reprFast(v_cidx_1035_);
v___x_1046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1044_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_box(1);
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_1036_);
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
return v___x_1053_;
}
case 4:
{
lean_object* v_x_1054_; lean_object* v_i_1055_; lean_object* v_y_1056_; lean_object* v_b_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_x_1054_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_x_1054_);
v_i_1055_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_i_1055_);
v_y_1056_ = lean_ctor_get(v_a_961_, 2);
lean_inc(v_y_1056_);
v_b_1057_ = lean_ctor_get(v_a_961_, 3);
lean_inc(v_b_1057_);
lean_dec_ref(v_a_961_);
v___x_1058_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_1059_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1060_ = l_Nat_reprFast(v_x_1054_);
v___x_1061_ = lean_string_append(v___x_1059_, v___x_1060_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1058_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Nat_reprFast(v_i_1055_);
v___x_1067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1065_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_1070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Nat_reprFast(v_y_1056_);
v___x_1072_ = lean_string_append(v___x_1059_, v___x_1071_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1070_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_box(1);
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_1057_);
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
return v___x_1080_;
}
case 5:
{
lean_object* v_x_1081_; lean_object* v_i_1082_; lean_object* v_offset_1083_; lean_object* v_y_1084_; lean_object* v_ty_1085_; lean_object* v_b_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_x_1081_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_x_1081_);
v_i_1082_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_i_1082_);
v_offset_1083_ = lean_ctor_get(v_a_961_, 2);
lean_inc(v_offset_1083_);
v_y_1084_ = lean_ctor_get(v_a_961_, 3);
lean_inc(v_y_1084_);
v_ty_1085_ = lean_ctor_get(v_a_961_, 4);
lean_inc(v_ty_1085_);
v_b_1086_ = lean_ctor_get(v_a_961_, 5);
lean_inc(v_b_1086_);
lean_dec_ref(v_a_961_);
v___x_1087_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__16));
v___x_1088_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1089_ = l_Nat_reprFast(v_x_1081_);
v___x_1090_ = lean_string_append(v___x_1088_, v___x_1089_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1087_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Nat_reprFast(v_i_1082_);
v___x_1096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1094_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Nat_reprFast(v_offset_1083_);
v___x_1101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1099_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__18));
v___x_1104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1085_);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__3));
v___x_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = l_Nat_reprFast(v_y_1084_);
v___x_1110_ = lean_string_append(v___x_1088_, v___x_1109_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1108_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_box(1);
v___x_1116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_1086_);
v___x_1118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
return v___x_1118_;
}
case 6:
{
lean_object* v_x_1119_; lean_object* v_n_1120_; lean_object* v_b_1121_; lean_object* v___x_1122_; lean_object* v___y_1124_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_x_1119_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_x_1119_);
v_n_1120_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_n_1120_);
v_b_1121_ = lean_ctor_get(v_a_961_, 2);
lean_inc(v_b_1121_);
lean_dec_ref(v_a_961_);
v___x_1122_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__20));
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_dec_eq(v_n_1120_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; 
v___x_1141_ = l_Nat_reprFast(v_n_1120_);
v___x_1142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
v___x_1143_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__22, &l_Lean_IR_formatFnBodyHead___closed__22_once, _init_l_Lean_IR_formatFnBodyHead___closed__22);
v___x_1144_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___x_1142_);
v___x_1146_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_1147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1143_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = 0;
v___x_1150_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*1, v___x_1149_);
v___y_1124_ = v___x_1150_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1151_; 
lean_dec(v_n_1120_);
v___x_1151_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___y_1124_ = v___x_1151_;
goto v___jp_1123_;
}
v___jp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1122_);
lean_ctor_set(v___x_1125_, 1, v___y_1124_);
v___x_1126_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_1127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1129_ = l_Nat_reprFast(v_x_1119_);
v___x_1130_ = lean_string_append(v___x_1128_, v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1127_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_box(1);
v___x_1136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_1121_);
v___x_1138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
return v___x_1138_;
}
}
case 7:
{
lean_object* v_x_1152_; lean_object* v_n_1153_; lean_object* v_b_1154_; lean_object* v___x_1155_; lean_object* v___y_1157_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_x_1152_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_x_1152_);
v_n_1153_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_n_1153_);
v_b_1154_ = lean_ctor_get(v_a_961_, 2);
lean_inc(v_b_1154_);
lean_dec_ref(v_a_961_);
v___x_1155_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__25));
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = lean_nat_dec_eq(v_n_1153_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1174_ = l_Nat_reprFast(v_n_1153_);
v___x_1175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
v___x_1176_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__22, &l_Lean_IR_formatFnBodyHead___closed__22_once, _init_l_Lean_IR_formatFnBodyHead___closed__22);
v___x_1177_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___x_1175_);
v___x_1179_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_1180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1176_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = 0;
v___x_1183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*1, v___x_1182_);
v___y_1157_ = v___x_1183_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1184_; 
lean_dec(v_n_1153_);
v___x_1184_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___y_1157_ = v___x_1184_;
goto v___jp_1156_;
}
v___jp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
lean_ctor_set(v___x_1158_, 1, v___y_1157_);
v___x_1159_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_1160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1162_ = l_Nat_reprFast(v_x_1152_);
v___x_1163_ = lean_string_append(v___x_1161_, v___x_1162_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1160_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_box(1);
v___x_1169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_1154_);
v___x_1171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
return v___x_1171_;
}
}
case 8:
{
lean_object* v_x_1185_; lean_object* v_b_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1204_; 
v_x_1185_ = lean_ctor_get(v_a_961_, 0);
v_b_1186_ = lean_ctor_get(v_a_961_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1188_ = v_a_961_;
v_isShared_1189_ = v_isSharedCheck_1204_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_b_1186_);
lean_inc(v_x_1185_);
lean_dec(v_a_961_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1204_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1190_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__27));
v___x_1191_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1192_ = l_Nat_reprFast(v_x_1185_);
v___x_1193_ = lean_string_append(v___x_1191_, v___x_1192_);
lean_dec_ref(v___x_1192_);
v___x_1194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 5);
lean_ctor_set(v___x_1188_, 1, v___x_1194_);
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1196_ = v___x_1188_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_box(1);
v___x_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_960_, v_b_1186_);
v___x_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
return v___x_1202_;
}
}
}
case 9:
{
lean_object* v_x_1205_; lean_object* v_xType_1206_; lean_object* v_cs_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_x_1205_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_x_1205_);
v_xType_1206_ = lean_ctor_get(v_a_961_, 2);
lean_inc(v_xType_1206_);
v_cs_1207_ = lean_ctor_get(v_a_961_, 3);
lean_inc_ref(v_cs_1207_);
lean_dec_ref(v_a_961_);
v___x_1208_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__29));
v___x_1209_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1210_ = l_Nat_reprFast(v_x_1205_);
v___x_1211_ = lean_string_append(v___x_1209_, v___x_1210_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1208_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_xType_1206_);
v___x_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5));
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_array_get_size(v_cs_1207_);
v___x_1223_ = lean_nat_dec_lt(v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_cs_1207_);
lean_dec(v_indent_960_);
v___x_1224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1219_);
lean_ctor_set(v___x_1224_, 1, v___x_1220_);
return v___x_1224_;
}
else
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_nat_dec_le(v___x_1222_, v___x_1222_);
if (v___x_1225_ == 0)
{
if (v___x_1223_ == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v_cs_1207_);
lean_dec(v_indent_960_);
v___x_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1219_);
lean_ctor_set(v___x_1226_, 1, v___x_1220_);
return v___x_1226_;
}
else
{
size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = ((size_t)0ULL);
v___x_1228_ = lean_usize_of_nat(v___x_1222_);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_960_, v_cs_1207_, v___x_1227_, v___x_1228_, v___x_1220_);
lean_dec_ref(v_cs_1207_);
v___x_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1219_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
return v___x_1230_;
}
}
else
{
size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = lean_usize_of_nat(v___x_1222_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_960_, v_cs_1207_, v___x_1231_, v___x_1232_, v___x_1220_);
lean_dec_ref(v_cs_1207_);
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1219_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
return v___x_1234_;
}
}
}
case 10:
{
lean_object* v_x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_indent_960_);
v_x_1235_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_x_1235_);
lean_dec_ref(v_a_961_);
v___x_1236_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__33));
v___x_1237_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_1235_);
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
return v___x_1238_;
}
case 11:
{
lean_object* v_j_1239_; lean_object* v_ys_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1254_; 
lean_dec(v_indent_960_);
v_j_1239_ = lean_ctor_get(v_a_961_, 0);
v_ys_1240_ = lean_ctor_get(v_a_961_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1242_ = v_a_961_;
v_isShared_1243_ = v_isSharedCheck_1254_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_ys_1240_);
lean_inc(v_j_1239_);
lean_dec(v_a_961_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1254_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1244_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__35));
v___x_1245_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_1246_ = l_Nat_reprFast(v_j_1239_);
v___x_1247_ = lean_string_append(v___x_1245_, v___x_1246_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set_tag(v___x_1242_, 5);
lean_ctor_set(v___x_1242_, 1, v___x_1248_);
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1250_ = v___x_1242_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1240_);
lean_dec_ref(v_ys_1240_);
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
return v___x_1252_;
}
}
}
default: 
{
lean_object* v___x_1255_; 
lean_dec(v_indent_960_);
v___x_1255_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__37));
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(lean_object* v_indent_1256_, lean_object* v_as_1257_, size_t v_i_1258_, size_t v_stop_1259_, lean_object* v_b_1260_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_usize_dec_eq(v_i_1258_, v_stop_1259_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; 
v___x_1262_ = lean_array_uget_borrowed(v_as_1257_, v_i_1258_);
v___x_1263_ = lean_box(1);
v___x_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_b_1260_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
lean_inc(v_indent_1256_);
v___x_1265_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop), 2, 1);
lean_closure_set(v___x_1265_, 0, v_indent_1256_);
lean_inc(v___x_1262_);
lean_inc(v_indent_1256_);
v___x_1266_ = l_Lean_IR_formatAlt(v___x_1265_, v_indent_1256_, v___x_1262_);
v___x_1267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1264_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_add(v_i_1258_, v___x_1268_);
v_i_1258_ = v___x_1269_;
v_b_1260_ = v___x_1267_;
goto _start;
}
else
{
lean_dec(v_indent_1256_);
return v_b_1260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0___boxed(lean_object* v_indent_1271_, lean_object* v_as_1272_, lean_object* v_i_1273_, lean_object* v_stop_1274_, lean_object* v_b_1275_){
_start:
{
size_t v_i_boxed_1276_; size_t v_stop_boxed_1277_; lean_object* v_res_1278_; 
v_i_boxed_1276_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_stop_boxed_1277_ = lean_unbox_usize(v_stop_1274_);
lean_dec(v_stop_1274_);
v_res_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_1271_, v_as_1272_, v_i_boxed_1276_, v_stop_boxed_1277_, v_b_1275_);
lean_dec_ref(v_as_1272_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody(lean_object* v_fnBody_1279_, lean_object* v_indent_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_1280_, v_fnBody_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatFnBody___lam__0(lean_object* v_fnBody_1282_){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_unsigned_to_nat(2u);
v___x_1284_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_1283_, v_fnBody_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringFnBody___lam__0(lean_object* v_b_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1288_ = lean_unsigned_to_nat(2u);
v___x_1289_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_1288_, v_b_1287_);
v___x_1290_ = l_Std_Format_defWidth;
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = l_Std_Format_pretty(v___x_1289_, v___x_1290_, v___x_1291_, v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatDecl(lean_object* v_decl_1301_, lean_object* v_indent_1302_){
_start:
{
if (lean_obj_tag(v_decl_1301_) == 0)
{
lean_object* v_f_1303_; lean_object* v_xs_1304_; lean_object* v_type_1305_; lean_object* v_body_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_f_1303_ = lean_ctor_get(v_decl_1301_, 0);
lean_inc(v_f_1303_);
v_xs_1304_ = lean_ctor_get(v_decl_1301_, 1);
lean_inc_ref(v_xs_1304_);
v_type_1305_ = lean_ctor_get(v_decl_1301_, 2);
lean_inc(v_type_1305_);
v_body_1306_ = lean_ctor_get(v_decl_1301_, 3);
lean_inc(v_body_1306_);
lean_dec_ref(v_decl_1301_);
v___x_1307_ = ((lean_object*)(l_Lean_IR_formatDecl___closed__1));
v___x_1308_ = 1;
v___x_1309_ = l_Lean_Name_toString(v_f_1303_, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1307_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_1304_);
lean_dec_ref(v_xs_1304_);
v___x_1313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_1305_);
v___x_1317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
lean_inc(v_indent_1302_);
v___x_1320_ = lean_nat_to_int(v_indent_1302_);
v___x_1321_ = lean_box(1);
v___x_1322_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_1302_, v_body_1306_);
v___x_1323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1320_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1319_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
return v___x_1325_;
}
else
{
lean_object* v_f_1326_; lean_object* v_xs_1327_; lean_object* v_type_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v_indent_1302_);
v_f_1326_ = lean_ctor_get(v_decl_1301_, 0);
lean_inc(v_f_1326_);
v_xs_1327_ = lean_ctor_get(v_decl_1301_, 1);
lean_inc_ref(v_xs_1327_);
v_type_1328_ = lean_ctor_get(v_decl_1301_, 2);
lean_inc(v_type_1328_);
lean_dec_ref(v_decl_1301_);
v___x_1329_ = ((lean_object*)(l_Lean_IR_formatDecl___closed__3));
v___x_1330_ = 1;
v___x_1331_ = l_Lean_Name_toString(v_f_1326_, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
v___x_1333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1329_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_1327_);
lean_dec_ref(v_xs_1327_);
v___x_1335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_1328_);
v___x_1339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatDecl___lam__0(lean_object* v_decl_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_unsigned_to_nat(2u);
v___x_1342_ = l_Lean_IR_formatDecl(v_decl_1340_, v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declToString(lean_object* v_d_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1346_ = lean_unsigned_to_nat(2u);
v___x_1347_ = l_Lean_IR_formatDecl(v_d_1345_, v___x_1346_);
v___x_1348_ = l_Std_Format_defWidth;
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = l_Std_Format_pretty(v___x_1347_, v___x_1348_, v___x_1349_, v___x_1349_);
return v___x_1350_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Format(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
