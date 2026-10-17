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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_targetVar(lean_object*);
lean_object* l_Lean_IR_FnBody_targetType(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isVarDecl(lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__1(lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Compiler.IR.Format"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__28 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__28_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Compiler.IR.Format.0.Lean.IR.formatExpr"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__29 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__29_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__30 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__30_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(lean_object*);
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
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "block_"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__0 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__0_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " := ..."};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__1 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__1_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__1_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__2 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__2_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "set "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__3 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__3_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__3_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__4 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__4_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "] := "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__5 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__5_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__5_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__6 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__6_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "uset "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__7 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__7_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__7_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__8 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__8_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sset "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__9 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__9_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__9_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__10 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__10_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "] : "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__11 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__11_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__11_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__12 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__12_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__13 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__13_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__13_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__14 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__14_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "setTag "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__15 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__15_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__15_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__16 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__16_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inc"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__17 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__17_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__17_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__18 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__18_value;
static lean_once_cell_t l_Lean_IR_formatFnBodyHead___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_formatFnBodyHead___closed__19;
static lean_once_cell_t l_Lean_IR_formatFnBodyHead___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_formatFnBodyHead___closed__20;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__21 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__21_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__22 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__22_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__22_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__23 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__23_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "del "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__24 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__24_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__24_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__25 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__25_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__26 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__26_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__26_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__27 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__27_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " of ..."};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__28 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__28_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__28_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__29 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__29_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "jmp "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__30 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__30_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__30_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__31 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__31_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ret "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__32 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__32_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__32_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__33 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__33_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊥"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__34 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__34_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__34_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__35 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__35_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.IR.formatFnBodyHead"};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__36 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__36_value;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: b.isVarDecl\n    "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__37 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__37_value;
static lean_once_cell_t l_Lean_IR_formatFnBodyHead___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_formatFnBodyHead___closed__38;
static const lean_string_object l_Lean_IR_formatFnBodyHead___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "let "};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__39 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__39_value;
static const lean_ctor_object l_Lean_IR_formatFnBodyHead___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_formatFnBodyHead___closed__39_value)}};
static const lean_object* l_Lean_IR_formatFnBodyHead___closed__40 = (const lean_object*)&l_Lean_IR_formatFnBodyHead___closed__40_value;
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBodyHead(lean_object*);
LEAN_EXPORT lean_object* lean_ir_format_fn_body_head(lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " :="};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__1(lean_object* v_msg_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_box(0);
v___x_141_ = lean_panic_fn_borrowed(v___x_140_, v_msg_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(lean_object* v_as_142_, size_t v_i_143_, size_t v_stop_144_, lean_object* v_b_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_usize_dec_eq(v_i_143_, v_stop_144_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; size_t v___x_152_; size_t v___x_153_; 
v___x_147_ = lean_array_uget_borrowed(v_as_142_, v_i_143_);
v___x_148_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v_b_145_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
lean_inc(v___x_147_);
v___x_150_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v___x_147_);
v___x_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_add(v_i_143_, v___x_152_);
v_i_143_ = v___x_153_;
v_b_145_ = v___x_151_;
goto _start;
}
else
{
return v_b_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0___boxed(lean_object* v_as_155_, lean_object* v_i_156_, lean_object* v_stop_157_, lean_object* v_b_158_){
_start:
{
size_t v_i_boxed_159_; size_t v_stop_boxed_160_; lean_object* v_res_161_; 
v_i_boxed_159_ = lean_unbox_usize(v_i_156_);
lean_dec(v_i_156_);
v_stop_boxed_160_ = lean_unbox_usize(v_stop_157_);
lean_dec(v_stop_157_);
v_res_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_as_155_, v_i_boxed_159_, v_stop_boxed_160_, v_b_158_);
lean_dec_ref(v_as_155_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(lean_object* v_args_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_array_get_size(v_args_162_);
v___x_166_ = lean_nat_dec_lt(v___x_164_, v___x_165_);
if (v___x_166_ == 0)
{
return v___x_163_;
}
else
{
size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((size_t)0ULL);
v___x_168_ = lean_usize_of_nat(v___x_165_);
v___x_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_162_, v___x_167_, v___x_168_, v___x_163_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(lean_object* v_args_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_args_170_);
lean_dec_ref(v_args_170_);
return v_res_171_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__30));
v___x_217_ = lean_unsigned_to_nat(9u);
v___x_218_ = lean_unsigned_to_nat(63u);
v___x_219_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__29));
v___x_220_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__28));
v___x_221_ = l_mkPanicMessageWithDecl(v___x_220_, v___x_219_, v___x_218_, v___x_217_, v___x_216_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(lean_object* v_x_222_){
_start:
{
uint64_t v_v_224_; 
switch(lean_obj_tag(v_x_222_))
{
case 0:
{
lean_object* v_i_228_; lean_object* v_ys_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_i_228_ = lean_ctor_get(v_x_222_, 2);
lean_inc_ref(v_i_228_);
v_ys_229_ = lean_ctor_get(v_x_222_, 3);
lean_inc_ref(v_ys_229_);
lean_dec_ref_known(v_x_222_, 4);
v___x_230_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_228_);
v___x_231_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_229_);
lean_dec_ref(v_ys_229_);
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
case 1:
{
lean_object* v_n_233_; lean_object* v_x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_n_233_ = lean_ctor_get(v_x_222_, 2);
lean_inc(v_n_233_);
v_x_234_ = lean_ctor_get(v_x_222_, 3);
lean_inc(v_x_234_);
lean_dec_ref_known(v_x_222_, 4);
v___x_235_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1));
v___x_236_ = l_Nat_reprFast(v_n_233_);
v___x_237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_235_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_242_ = l_Nat_reprFast(v_x_234_);
v___x_243_ = lean_string_append(v___x_241_, v___x_242_);
lean_dec_ref(v___x_242_);
v___x_244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
v___x_245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_240_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
return v___x_245_;
}
case 2:
{
lean_object* v_x_246_; lean_object* v_i_247_; uint8_t v_updtHeader_248_; lean_object* v_ys_249_; lean_object* v___x_250_; lean_object* v___y_252_; 
v_x_246_ = lean_ctor_get(v_x_222_, 2);
lean_inc(v_x_246_);
v_i_247_ = lean_ctor_get(v_x_222_, 3);
lean_inc_ref(v_i_247_);
v_updtHeader_248_ = lean_ctor_get_uint8(v_x_222_, sizeof(void*)*5);
v_ys_249_ = lean_ctor_get(v_x_222_, 4);
lean_inc_ref(v_ys_249_);
lean_dec_ref_known(v_x_222_, 5);
v___x_250_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5));
if (v_updtHeader_248_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8));
v___y_252_ = v___x_268_;
goto v___jp_251_;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9));
v___y_252_ = v___x_269_;
goto v___jp_251_;
}
v___jp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_inc_ref(v___y_252_);
v___x_253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_253_, 0, v___y_252_);
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_250_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_258_ = l_Nat_reprFast(v_x_246_);
v___x_259_ = lean_string_append(v___x_257_, v___x_258_);
lean_dec_ref(v___x_258_);
v___x_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_256_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7));
v___x_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_247_);
v___x_265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_249_);
lean_dec_ref(v_ys_249_);
v___x_267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
return v___x_267_;
}
}
case 3:
{
lean_object* v_i_270_; lean_object* v_x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_i_270_ = lean_ctor_get(v_x_222_, 2);
lean_inc(v_i_270_);
v_x_271_ = lean_ctor_get(v_x_222_, 3);
lean_inc(v_x_271_);
lean_dec_ref_known(v_x_222_, 4);
v___x_272_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11));
v___x_273_ = l_Nat_reprFast(v_i_270_);
v___x_274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_272_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_279_ = l_Nat_reprFast(v_x_271_);
v___x_280_ = lean_string_append(v___x_278_, v___x_279_);
lean_dec_ref(v___x_279_);
v___x_281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_277_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
return v___x_282_;
}
case 4:
{
lean_object* v_i_283_; lean_object* v_x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_i_283_ = lean_ctor_get(v_x_222_, 2);
lean_inc(v_i_283_);
v_x_284_ = lean_ctor_get(v_x_222_, 3);
lean_inc(v_x_284_);
lean_dec_ref_known(v_x_222_, 4);
v___x_285_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13));
v___x_286_ = l_Nat_reprFast(v_i_283_);
v___x_287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_292_ = l_Nat_reprFast(v_x_284_);
v___x_293_ = lean_string_append(v___x_291_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_290_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
case 5:
{
lean_object* v_n_296_; lean_object* v_offset_297_; lean_object* v_x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_n_296_ = lean_ctor_get(v_x_222_, 3);
lean_inc(v_n_296_);
v_offset_297_ = lean_ctor_get(v_x_222_, 4);
lean_inc(v_offset_297_);
v_x_298_ = lean_ctor_get(v_x_222_, 5);
lean_inc(v_x_298_);
lean_dec_ref_known(v_x_222_, 6);
v___x_299_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15));
v___x_300_ = l_Nat_reprFast(v_n_296_);
v___x_301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
v___x_302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_299_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Nat_reprFast(v_offset_297_);
v___x_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_304_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_311_ = l_Nat_reprFast(v_x_298_);
v___x_312_ = lean_string_append(v___x_310_, v___x_311_);
lean_dec_ref(v___x_311_);
v___x_313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_309_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
return v___x_314_;
}
case 6:
{
lean_object* v_c_315_; lean_object* v_ys_316_; uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_c_315_ = lean_ctor_get(v_x_222_, 3);
lean_inc(v_c_315_);
v_ys_316_ = lean_ctor_get(v_x_222_, 4);
lean_inc_ref(v_ys_316_);
lean_dec_ref_known(v_x_222_, 5);
v___x_317_ = 1;
v___x_318_ = l_Lean_Name_toString(v_c_315_, v___x_317_);
v___x_319_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
v___x_320_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_316_);
lean_dec_ref(v_ys_316_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
return v___x_321_;
}
case 7:
{
lean_object* v_c_322_; lean_object* v_ys_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_c_322_ = lean_ctor_get(v_x_222_, 2);
lean_inc(v_c_322_);
v_ys_323_ = lean_ctor_get(v_x_222_, 3);
lean_inc_ref(v_ys_323_);
lean_dec_ref_known(v_x_222_, 4);
v___x_324_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19));
v___x_325_ = 1;
v___x_326_ = l_Lean_Name_toString(v_c_322_, v___x_325_);
v___x_327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_324_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_323_);
lean_dec_ref(v_ys_323_);
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
return v___x_330_;
}
case 8:
{
lean_object* v_x_331_; lean_object* v_ys_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_x_331_ = lean_ctor_get(v_x_222_, 2);
lean_inc(v_x_331_);
v_ys_332_ = lean_ctor_get(v_x_222_, 3);
lean_inc_ref(v_ys_332_);
lean_dec_ref_known(v_x_222_, 4);
v___x_333_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21));
v___x_334_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_335_ = l_Nat_reprFast(v_x_331_);
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
lean_dec_ref(v___x_335_);
v___x_337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
v___x_338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_333_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_332_);
lean_dec_ref(v_ys_332_);
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
return v___x_340_;
}
case 9:
{
lean_object* v_x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_x_341_ = lean_ctor_get(v_x_222_, 3);
lean_inc(v_x_341_);
lean_dec_ref_known(v_x_222_, 4);
v___x_342_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23));
v___x_343_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_344_ = l_Nat_reprFast(v_x_341_);
v___x_345_ = lean_string_append(v___x_343_, v___x_344_);
lean_dec_ref(v___x_344_);
v___x_346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_342_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
case 10:
{
lean_object* v_x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_x_348_ = lean_ctor_get(v_x_222_, 3);
lean_inc(v_x_348_);
lean_dec_ref_known(v_x_222_, 4);
v___x_349_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25));
v___x_350_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_351_ = l_Nat_reprFast(v_x_348_);
v___x_352_ = lean_string_append(v___x_350_, v___x_351_);
lean_dec_ref(v___x_351_);
v___x_353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
v___x_354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_349_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
return v___x_354_;
}
case 11:
{
uint8_t v_v_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_v_355_ = lean_ctor_get_uint8(v_x_222_, sizeof(void*)*2);
lean_dec_ref_known(v_x_222_, 2);
v___x_356_ = lean_uint8_to_nat(v_v_355_);
v___x_357_ = l_Nat_reprFast(v___x_356_);
v___x_358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
case 12:
{
uint16_t v_v_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_v_359_ = lean_ctor_get_uint16(v_x_222_, sizeof(void*)*2);
lean_dec_ref_known(v_x_222_, 2);
v___x_360_ = lean_uint16_to_nat(v_v_359_);
v___x_361_ = l_Nat_reprFast(v___x_360_);
v___x_362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
case 13:
{
uint32_t v_v_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_v_363_ = lean_ctor_get_uint32(v_x_222_, sizeof(void*)*2);
lean_dec_ref_known(v_x_222_, 2);
v___x_364_ = lean_uint32_to_nat(v_v_363_);
v___x_365_ = l_Nat_reprFast(v___x_364_);
v___x_366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
case 14:
{
uint64_t v_v_367_; 
v_v_367_ = lean_ctor_get_uint64(v_x_222_, sizeof(void*)*2);
lean_dec_ref_known(v_x_222_, 2);
v_v_224_ = v_v_367_;
goto v___jp_223_;
}
case 15:
{
uint64_t v_v_368_; 
v_v_368_ = lean_ctor_get_uint64(v_x_222_, sizeof(void*)*2);
lean_dec_ref_known(v_x_222_, 2);
v_v_224_ = v_v_368_;
goto v___jp_223_;
}
case 16:
{
lean_object* v_v_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_v_369_ = lean_ctor_get(v_x_222_, 2);
lean_inc(v_v_369_);
lean_dec_ref_known(v_x_222_, 3);
v___x_370_ = l_Nat_reprFast(v_v_369_);
v___x_371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
case 17:
{
lean_object* v_v_372_; lean_object* v___x_373_; 
v_v_372_ = lean_ctor_get(v_x_222_, 2);
lean_inc_ref(v_v_372_);
lean_dec_ref_known(v_x_222_, 3);
v___x_373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_373_, 0, v_v_372_);
return v___x_373_;
}
case 18:
{
lean_object* v_x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_x_374_ = lean_ctor_get(v_x_222_, 2);
lean_inc(v_x_374_);
lean_dec_ref_known(v_x_222_, 3);
v___x_375_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27));
v___x_376_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_377_ = l_Nat_reprFast(v_x_374_);
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
lean_dec_ref(v___x_377_);
v___x_379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_375_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
return v___x_380_;
}
default: 
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_x_222_);
v___x_381_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31);
v___x_382_ = l_panic___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__1(v___x_381_);
return v___x_382_;
}
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_uint64_to_nat(v_v_224_);
v___x_226_ = l_Nat_reprFast(v___x_225_);
v___x_227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__1(lean_object* v_a_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_nat_to_int(v_a_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v___x_417_; 
lean_dec(v_x_416_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
else
{
lean_object* v_tail_418_; 
v_tail_418_ = lean_ctor_get(v_x_415_, 1);
if (lean_obj_tag(v_tail_418_) == 0)
{
lean_object* v_head_419_; lean_object* v___x_420_; 
lean_dec(v_x_416_);
v_head_419_ = lean_ctor_get(v_x_415_, 0);
lean_inc(v_head_419_);
lean_dec_ref_known(v_x_415_, 2);
v___x_420_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_419_);
return v___x_420_;
}
else
{
lean_object* v_head_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_inc(v_tail_418_);
v_head_421_ = lean_ctor_get(v_x_415_, 0);
lean_inc(v_head_421_);
lean_dec_ref_known(v_x_415_, 2);
v___x_422_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_421_);
v___x_423_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(v_x_416_, v___x_422_, v_tail_418_);
return v___x_423_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20));
v___x_426_ = lean_string_length(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22);
v___x_428_ = lean_nat_to_int(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object* v_x_443_){
_start:
{
switch(lean_obj_tag(v_x_443_))
{
case 0:
{
lean_object* v___x_444_; 
v___x_444_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1));
return v___x_444_;
}
case 1:
{
lean_object* v___x_445_; 
v___x_445_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3));
return v___x_445_;
}
case 2:
{
lean_object* v___x_446_; 
v___x_446_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5));
return v___x_446_;
}
case 3:
{
lean_object* v___x_447_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7));
return v___x_447_;
}
case 4:
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9));
return v___x_448_;
}
case 5:
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11));
return v___x_449_;
}
case 6:
{
lean_object* v___x_450_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2));
return v___x_450_;
}
case 7:
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13));
return v___x_451_;
}
case 8:
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15));
return v___x_452_;
}
case 9:
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17));
return v___x_453_;
}
case 10:
{
lean_object* v_types_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_473_; 
v_types_454_ = lean_ctor_get(v_x_443_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_x_443_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v_x_443_, 0);
lean_dec(v_unused_474_);
v___x_456_ = v_x_443_;
v_isShared_457_ = v_isSharedCheck_473_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_types_454_);
lean_dec(v_x_443_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_473_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19));
v___x_459_ = lean_array_to_list(v_types_454_);
v___x_460_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_461_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_459_, v___x_460_);
v___x_462_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
v___x_463_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24));
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 5);
lean_ctor_set(v___x_456_, 1, v___x_461_);
lean_ctor_set(v___x_456_, 0, v___x_463_);
v___x_465_ = v___x_456_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_461_);
v___x_465_ = v_reuseFailAlloc_472_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_466_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25));
v___x_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_462_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = 0;
v___x_470_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*1, v___x_469_);
v___x_471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_458_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
return v___x_471_;
}
}
}
case 11:
{
lean_object* v_types_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_494_; 
v_types_475_ = lean_ctor_get(v_x_443_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_x_443_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v_x_443_, 0);
lean_dec(v_unused_495_);
v___x_477_ = v_x_443_;
v_isShared_478_ = v_isSharedCheck_494_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_types_475_);
lean_dec(v_x_443_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_494_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_479_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27));
v___x_480_ = lean_array_to_list(v_types_475_);
v___x_481_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_482_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_480_, v___x_481_);
v___x_483_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
v___x_484_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24));
if (v_isShared_478_ == 0)
{
lean_ctor_set_tag(v___x_477_, 5);
lean_ctor_set(v___x_477_, 1, v___x_482_);
lean_ctor_set(v___x_477_, 0, v___x_484_);
v___x_486_ = v___x_477_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_482_);
v___x_486_ = v_reuseFailAlloc_493_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25));
v___x_488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_483_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = 0;
v___x_491_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*1, v___x_490_);
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_479_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
return v___x_492_;
}
}
}
case 12:
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29));
return v___x_496_;
}
default: 
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31));
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_dec(v_x_498_);
return v_x_499_;
}
else
{
lean_object* v_head_501_; lean_object* v_tail_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_512_; 
v_head_501_ = lean_ctor_get(v_x_500_, 0);
v_tail_502_ = lean_ctor_get(v_x_500_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_512_ == 0)
{
v___x_504_ = v_x_500_;
v_isShared_505_ = v_isSharedCheck_512_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_tail_502_);
lean_inc(v_head_501_);
lean_dec(v_x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_512_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
lean_inc(v_x_498_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 5);
lean_ctor_set(v___x_504_, 1, v_x_498_);
lean_ctor_set(v___x_504_, 0, v_x_499_);
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_x_499_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_x_498_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_501_);
v___x_509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v_x_499_ = v___x_509_;
v_x_500_ = v_tail_502_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatIRType___private__1(lean_object* v_a_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringIRType___lam__0(lean_object* v_f_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = l_Std_Format_defWidth;
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = l_Std_Format_pretty(v_f_517_, v___x_518_, v___x_519_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(lean_object* v_x_536_){
_start:
{
lean_object* v_x_537_; uint8_t v_borrow_538_; lean_object* v_ty_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___y_549_; 
v_x_537_ = lean_ctor_get(v_x_536_, 0);
lean_inc(v_x_537_);
v_borrow_538_ = lean_ctor_get_uint8(v_x_536_, sizeof(void*)*2);
v_ty_539_ = lean_ctor_get(v_x_536_, 1);
lean_inc(v_ty_539_);
lean_dec_ref(v_x_536_);
v___x_540_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1));
v___x_541_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_542_ = l_Nat_reprFast(v_x_537_);
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_540_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
if (v_borrow_538_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8));
v___y_549_ = v___x_556_;
goto v___jp_548_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6));
v___y_549_ = v___x_557_;
goto v___jp_548_;
}
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc_ref(v___y_549_);
v___x_550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_550_, 0, v___y_549_);
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_547_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_539_);
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5));
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatParam___private__1(lean_object* v_a_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v_a_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatAlt(lean_object* v_fmt_568_, lean_object* v_indent_569_, lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v_info_571_; lean_object* v_b_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_590_; 
v_info_571_ = lean_ctor_get(v_x_570_, 0);
v_b_572_ = lean_ctor_get(v_x_570_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_590_ == 0)
{
v___x_574_ = v_x_570_;
v_isShared_575_ = v_isSharedCheck_590_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_b_572_);
lean_inc(v_info_571_);
lean_dec(v_x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_590_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_name_576_; uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v_name_576_ = lean_ctor_get(v_info_571_, 0);
lean_inc(v_name_576_);
lean_dec_ref(v_info_571_);
v___x_577_ = 1;
v___x_578_ = l_Lean_Name_toString(v_name_576_, v___x_577_);
v___x_579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
v___x_580_ = ((lean_object*)(l_Lean_IR_formatAlt___closed__1));
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 5);
lean_ctor_set(v___x_574_, 1, v___x_580_);
lean_ctor_set(v___x_574_, 0, v___x_579_);
v___x_582_ = v___x_574_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_589_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_583_ = lean_nat_to_int(v_indent_569_);
v___x_584_ = lean_box(1);
v___x_585_ = lean_apply_1(v_fmt_568_, v_b_572_);
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_583_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_582_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
return v___x_588_;
}
}
}
else
{
lean_object* v_b_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_b_591_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_b_591_);
lean_dec_ref_known(v_x_570_, 1);
v___x_592_ = ((lean_object*)(l_Lean_IR_formatAlt___closed__3));
v___x_593_ = lean_nat_to_int(v_indent_569_);
v___x_594_ = lean_box(1);
v___x_595_ = lean_apply_1(v_fmt_568_, v_b_591_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_593_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_592_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(lean_object* v_as_599_, size_t v_i_600_, size_t v_stop_601_, lean_object* v_b_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = lean_usize_dec_eq(v_i_600_, v_stop_601_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; size_t v___x_609_; size_t v___x_610_; 
v___x_604_ = lean_array_uget_borrowed(v_as_599_, v_i_600_);
v___x_605_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v_b_602_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
lean_inc(v___x_604_);
v___x_607_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v___x_604_);
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_600_, v___x_609_);
v_i_600_ = v___x_610_;
v_b_602_ = v___x_608_;
goto _start;
}
else
{
return v_b_602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0___boxed(lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_stop_614_, lean_object* v_b_615_){
_start:
{
size_t v_i_boxed_616_; size_t v_stop_boxed_617_; lean_object* v_res_618_; 
v_i_boxed_616_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_stop_boxed_617_ = lean_unbox_usize(v_stop_614_);
lean_dec(v_stop_614_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_as_612_, v_i_boxed_616_, v_stop_boxed_617_, v_b_615_);
lean_dec_ref(v_as_612_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(lean_object* v_args_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_620_ = lean_box(0);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_array_get_size(v_args_619_);
v___x_623_ = lean_nat_dec_lt(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
return v___x_620_;
}
else
{
size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((size_t)0ULL);
v___x_625_ = lean_usize_of_nat(v___x_622_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_619_, v___x_624_, v___x_625_, v___x_620_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0___boxed(lean_object* v_args_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_args_627_);
lean_dec_ref(v_args_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams(lean_object* v_ps_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_ps_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams___boxed(lean_object* v_ps_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_IR_formatParams(v_ps_631_);
lean_dec_ref(v_ps_631_);
return v_res_632_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__19(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0));
v___x_662_ = lean_string_length(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__20(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__19, &l_Lean_IR_formatFnBodyHead___closed__19_once, _init_l_Lean_IR_formatFnBodyHead___closed__19);
v___x_664_ = lean_nat_to_int(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__38(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_690_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__37));
v___x_691_ = lean_unsigned_to_nat(4u);
v___x_692_ = lean_unsigned_to_nat(114u);
v___x_693_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__36));
v___x_694_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__28));
v___x_695_ = l_mkPanicMessageWithDecl(v___x_694_, v___x_693_, v___x_692_, v___x_691_, v___x_690_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBodyHead(lean_object* v_x_699_){
_start:
{
switch(lean_obj_tag(v_x_699_))
{
case 19:
{
lean_object* v_j_700_; lean_object* v_xs_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_j_700_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_j_700_);
v_xs_701_ = lean_ctor_get(v_x_699_, 1);
lean_inc_ref(v_xs_701_);
lean_dec_ref_known(v_x_699_, 4);
v___x_702_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__0));
v___x_703_ = l_Nat_reprFast(v_j_700_);
v___x_704_ = lean_string_append(v___x_702_, v___x_703_);
lean_dec_ref(v___x_703_);
v___x_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
v___x_706_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_701_);
lean_dec_ref(v_xs_701_);
v___x_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__2));
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
return v___x_709_;
}
case 20:
{
lean_object* v_x_710_; lean_object* v_i_711_; lean_object* v_y_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_x_710_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_x_710_);
v_i_711_ = lean_ctor_get(v_x_699_, 1);
lean_inc(v_i_711_);
v_y_712_ = lean_ctor_get(v_x_699_, 2);
lean_inc(v_y_712_);
lean_dec_ref_known(v_x_699_, 4);
v___x_713_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_714_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_715_ = l_Nat_reprFast(v_x_710_);
v___x_716_ = lean_string_append(v___x_714_, v___x_715_);
lean_dec_ref(v___x_715_);
v___x_717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_713_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Nat_reprFast(v_i_711_);
v___x_722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_720_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_712_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
return v___x_727_;
}
case 22:
{
lean_object* v_x_728_; lean_object* v_i_729_; lean_object* v_y_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_x_728_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_x_728_);
v_i_729_ = lean_ctor_get(v_x_699_, 1);
lean_inc(v_i_729_);
v_y_730_ = lean_ctor_get(v_x_699_, 2);
lean_inc(v_y_730_);
lean_dec_ref_known(v_x_699_, 4);
v___x_731_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__8));
v___x_732_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_733_ = l_Nat_reprFast(v_x_728_);
v___x_734_ = lean_string_append(v___x_732_, v___x_733_);
lean_dec_ref(v___x_733_);
v___x_735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_731_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Nat_reprFast(v_i_729_);
v___x_740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
v___x_741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_738_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Nat_reprFast(v_y_730_);
v___x_745_ = lean_string_append(v___x_732_, v___x_744_);
lean_dec_ref(v___x_744_);
v___x_746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
v___x_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_743_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
return v___x_747_;
}
case 23:
{
lean_object* v_x_748_; lean_object* v_i_749_; lean_object* v_offset_750_; lean_object* v_y_751_; lean_object* v_ty_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_x_748_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_x_748_);
v_i_749_ = lean_ctor_get(v_x_699_, 1);
lean_inc(v_i_749_);
v_offset_750_ = lean_ctor_get(v_x_699_, 2);
lean_inc(v_offset_750_);
v_y_751_ = lean_ctor_get(v_x_699_, 3);
lean_inc(v_y_751_);
v_ty_752_ = lean_ctor_get(v_x_699_, 4);
lean_inc(v_ty_752_);
lean_dec_ref_known(v_x_699_, 6);
v___x_753_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_754_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_755_ = l_Nat_reprFast(v_x_748_);
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
lean_dec_ref(v___x_755_);
v___x_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_753_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Nat_reprFast(v_i_749_);
v___x_762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_760_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Nat_reprFast(v_offset_750_);
v___x_767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
v___x_768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_765_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__12));
v___x_770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_752_);
v___x_772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Nat_reprFast(v_y_751_);
v___x_776_ = lean_string_append(v___x_754_, v___x_775_);
lean_dec_ref(v___x_775_);
v___x_777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
v___x_778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_774_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
return v___x_778_;
}
case 21:
{
lean_object* v_x_779_; lean_object* v_cidx_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_x_779_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_x_779_);
v_cidx_780_ = lean_ctor_get(v_x_699_, 1);
lean_inc(v_cidx_780_);
lean_dec_ref_known(v_x_699_, 3);
v___x_781_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__16));
v___x_782_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_783_ = l_Nat_reprFast(v_x_779_);
v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
v___x_786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_781_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Nat_reprFast(v_cidx_780_);
v___x_790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_788_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
return v___x_791_;
}
case 24:
{
lean_object* v_x_792_; lean_object* v_n_793_; lean_object* v___x_794_; lean_object* v___y_796_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_x_792_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_x_792_);
v_n_793_ = lean_ctor_get(v_x_699_, 1);
lean_inc(v_n_793_);
lean_dec_ref_known(v_x_699_, 3);
v___x_794_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__18));
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_dec_eq(v_n_793_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; 
v___x_807_ = l_Nat_reprFast(v_n_793_);
v___x_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__20, &l_Lean_IR_formatFnBodyHead___closed__20_once, _init_l_Lean_IR_formatFnBodyHead___closed__20);
v___x_810_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_808_);
v___x_812_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_809_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = 0;
v___x_816_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_815_);
v___y_796_ = v___x_816_;
goto v___jp_795_;
}
else
{
lean_object* v___x_817_; 
lean_dec(v_n_793_);
v___x_817_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__21));
v___y_796_ = v___x_817_;
goto v___jp_795_;
}
v___jp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_794_);
lean_ctor_set(v___x_797_, 1, v___y_796_);
v___x_798_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_801_ = l_Nat_reprFast(v_x_792_);
v___x_802_ = lean_string_append(v___x_800_, v___x_801_);
lean_dec_ref(v___x_801_);
v___x_803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___x_804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_799_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
return v___x_804_;
}
}
case 25:
{
lean_object* v_x_818_; lean_object* v_n_819_; lean_object* v___x_820_; lean_object* v___y_822_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_x_818_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_x_818_);
v_n_819_ = lean_ctor_get(v_x_699_, 1);
lean_inc(v_n_819_);
lean_dec_ref_known(v_x_699_, 3);
v___x_820_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_dec_eq(v_n_819_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; 
v___x_833_ = l_Nat_reprFast(v_n_819_);
v___x_834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
v___x_835_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__20, &l_Lean_IR_formatFnBodyHead___closed__20_once, _init_l_Lean_IR_formatFnBodyHead___closed__20);
v___x_836_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_834_);
v___x_838_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_835_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = 0;
v___x_842_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*1, v___x_841_);
v___y_822_ = v___x_842_;
goto v___jp_821_;
}
else
{
lean_object* v___x_843_; 
lean_dec(v_n_819_);
v___x_843_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__21));
v___y_822_ = v___x_843_;
goto v___jp_821_;
}
v___jp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_820_);
lean_ctor_set(v___x_823_, 1, v___y_822_);
v___x_824_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_827_ = l_Nat_reprFast(v_x_818_);
v___x_828_ = lean_string_append(v___x_826_, v___x_827_);
lean_dec_ref(v___x_827_);
v___x_829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_825_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
}
case 26:
{
lean_object* v_x_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_856_; 
v_x_844_ = lean_ctor_get(v_x_699_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_699_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_x_699_, 1);
lean_dec(v_unused_857_);
v___x_846_ = v_x_699_;
v_isShared_847_ = v_isSharedCheck_856_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_x_844_);
lean_dec(v_x_699_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_856_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_848_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__25));
v___x_849_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_850_ = l_Nat_reprFast(v_x_844_);
v___x_851_ = lean_string_append(v___x_849_, v___x_850_);
lean_dec_ref(v___x_850_);
v___x_852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 5);
lean_ctor_set(v___x_846_, 1, v___x_852_);
lean_ctor_set(v___x_846_, 0, v___x_848_);
v___x_854_ = v___x_846_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
case 27:
{
lean_object* v_x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_x_858_ = lean_ctor_get(v_x_699_, 1);
lean_inc(v_x_858_);
lean_dec_ref_known(v_x_699_, 4);
v___x_859_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__27));
v___x_860_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_861_ = l_Nat_reprFast(v_x_858_);
v___x_862_ = lean_string_append(v___x_860_, v___x_861_);
lean_dec_ref(v___x_861_);
v___x_863_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_859_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__29));
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
return v___x_866_;
}
case 29:
{
lean_object* v_j_867_; lean_object* v_ys_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_882_; 
v_j_867_ = lean_ctor_get(v_x_699_, 0);
v_ys_868_ = lean_ctor_get(v_x_699_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_x_699_);
if (v_isSharedCheck_882_ == 0)
{
v___x_870_ = v_x_699_;
v_isShared_871_ = v_isSharedCheck_882_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_ys_868_);
lean_inc(v_j_867_);
lean_dec(v_x_699_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_882_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_872_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__31));
v___x_873_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__0));
v___x_874_ = l_Nat_reprFast(v_j_867_);
v___x_875_ = lean_string_append(v___x_873_, v___x_874_);
lean_dec_ref(v___x_874_);
v___x_876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 5);
lean_ctor_set(v___x_870_, 1, v___x_876_);
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_878_ = v___x_870_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_881_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_868_);
lean_dec_ref(v_ys_868_);
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
return v___x_880_;
}
}
}
case 28:
{
lean_object* v_x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_x_883_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_x_883_);
lean_dec_ref_known(v_x_699_, 1);
v___x_884_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__33));
v___x_885_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_883_);
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
return v___x_886_;
}
case 30:
{
lean_object* v___x_887_; 
v___x_887_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__35));
return v___x_887_;
}
default: 
{
uint8_t v___x_888_; 
v___x_888_ = l_Lean_IR_FnBody_isVarDecl(v_x_699_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v_x_699_);
v___x_889_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__38, &l_Lean_IR_formatFnBodyHead___closed__38_once, _init_l_Lean_IR_formatFnBodyHead___closed__38);
v___x_890_ = l_panic___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__1(v___x_889_);
return v___x_890_;
}
else
{
lean_object* v_x_891_; lean_object* v_ty_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_x_891_ = l_Lean_IR_FnBody_targetVar(v_x_699_);
v_ty_892_ = l_Lean_IR_FnBody_targetType(v_x_699_);
v___x_893_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__40));
v___x_894_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_895_ = l_Nat_reprFast(v_x_891_);
v___x_896_ = lean_string_append(v___x_894_, v___x_895_);
lean_dec_ref(v___x_895_);
v___x_897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_893_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_892_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_x_699_);
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_format_fn_body_head(lean_object* v_fn_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = l_Lean_IR_formatFnBodyHead(v_fn_907_);
v___x_909_ = l_Std_Format_defWidth;
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = l_Std_Format_pretty(v___x_908_, v___x_909_, v___x_910_, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(lean_object* v_indent_921_, lean_object* v_a_922_){
_start:
{
switch(lean_obj_tag(v_a_922_))
{
case 19:
{
lean_object* v_j_923_; lean_object* v_xs_924_; lean_object* v_v_925_; lean_object* v_b_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_j_923_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_j_923_);
v_xs_924_ = lean_ctor_get(v_a_922_, 1);
lean_inc_ref(v_xs_924_);
v_v_925_ = lean_ctor_get(v_a_922_, 2);
lean_inc(v_v_925_);
v_b_926_ = lean_ctor_get(v_a_922_, 3);
lean_inc(v_b_926_);
lean_dec_ref_known(v_a_922_, 4);
v___x_927_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__0));
v___x_928_ = l_Nat_reprFast(v_j_923_);
v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
lean_dec_ref(v___x_928_);
v___x_930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
v___x_931_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_924_);
lean_dec_ref(v_xs_924_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_inc_n(v_indent_921_, 2);
v___x_935_ = lean_nat_to_int(v_indent_921_);
v___x_936_ = lean_box(1);
v___x_937_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_v_925_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_935_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_934_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_936_);
v___x_944_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_926_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
return v___x_945_;
}
case 20:
{
lean_object* v_x_946_; lean_object* v_i_947_; lean_object* v_y_948_; lean_object* v_b_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_x_946_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_x_946_);
v_i_947_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_i_947_);
v_y_948_ = lean_ctor_get(v_a_922_, 2);
lean_inc(v_y_948_);
v_b_949_ = lean_ctor_get(v_a_922_, 3);
lean_inc(v_b_949_);
lean_dec_ref_known(v_a_922_, 4);
v___x_950_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_951_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_952_ = l_Nat_reprFast(v_x_946_);
v___x_953_ = lean_string_append(v___x_951_, v___x_952_);
lean_dec_ref(v___x_952_);
v___x_954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_950_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Nat_reprFast(v_i_947_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_957_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_948_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_box(1);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_949_);
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
return v___x_970_;
}
case 22:
{
lean_object* v_x_971_; lean_object* v_i_972_; lean_object* v_y_973_; lean_object* v_b_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_x_971_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_x_971_);
v_i_972_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_i_972_);
v_y_973_ = lean_ctor_get(v_a_922_, 2);
lean_inc(v_y_973_);
v_b_974_ = lean_ctor_get(v_a_922_, 3);
lean_inc(v_b_974_);
lean_dec_ref_known(v_a_922_, 4);
v___x_975_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__8));
v___x_976_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_977_ = l_Nat_reprFast(v_x_971_);
v___x_978_ = lean_string_append(v___x_976_, v___x_977_);
lean_dec_ref(v___x_977_);
v___x_979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_975_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Nat_reprFast(v_i_972_);
v___x_984_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_982_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Nat_reprFast(v_y_973_);
v___x_989_ = lean_string_append(v___x_976_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_987_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_box(1);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_974_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
return v___x_997_;
}
case 23:
{
lean_object* v_x_998_; lean_object* v_i_999_; lean_object* v_offset_1000_; lean_object* v_y_1001_; lean_object* v_ty_1002_; lean_object* v_b_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_x_998_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_x_998_);
v_i_999_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_i_999_);
v_offset_1000_ = lean_ctor_get(v_a_922_, 2);
lean_inc(v_offset_1000_);
v_y_1001_ = lean_ctor_get(v_a_922_, 3);
lean_inc(v_y_1001_);
v_ty_1002_ = lean_ctor_get(v_a_922_, 4);
lean_inc(v_ty_1002_);
v_b_1003_ = lean_ctor_get(v_a_922_, 5);
lean_inc(v_b_1003_);
lean_dec_ref_known(v_a_922_, 6);
v___x_1004_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_1005_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1006_ = l_Nat_reprFast(v_x_998_);
v___x_1007_ = lean_string_append(v___x_1005_, v___x_1006_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1004_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Nat_reprFast(v_i_999_);
v___x_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Nat_reprFast(v_offset_1000_);
v___x_1018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1016_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__12));
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1002_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Nat_reprFast(v_y_1001_);
v___x_1027_ = lean_string_append(v___x_1005_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1025_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_box(1);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_1003_);
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
return v___x_1035_;
}
case 21:
{
lean_object* v_x_1036_; lean_object* v_cidx_1037_; lean_object* v_b_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_x_1036_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_x_1036_);
v_cidx_1037_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_cidx_1037_);
v_b_1038_ = lean_ctor_get(v_a_922_, 2);
lean_inc(v_b_1038_);
lean_dec_ref_known(v_a_922_, 3);
v___x_1039_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__16));
v___x_1040_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1041_ = l_Nat_reprFast(v_x_1036_);
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1039_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Nat_reprFast(v_cidx_1037_);
v___x_1048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1046_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_box(1);
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_1038_);
v___x_1055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
return v___x_1055_;
}
case 24:
{
lean_object* v_x_1056_; lean_object* v_n_1057_; lean_object* v_b_1058_; lean_object* v___x_1059_; lean_object* v___y_1061_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_x_1056_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_x_1056_);
v_n_1057_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_n_1057_);
v_b_1058_ = lean_ctor_get(v_a_922_, 2);
lean_inc(v_b_1058_);
lean_dec_ref_known(v_a_922_, 3);
v___x_1059_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__18));
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_dec_eq(v_n_1057_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1078_ = l_Nat_reprFast(v_n_1057_);
v___x_1079_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__20, &l_Lean_IR_formatFnBodyHead___closed__20_once, _init_l_Lean_IR_formatFnBodyHead___closed__20);
v___x_1081_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1079_);
v___x_1083_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1080_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = 0;
v___x_1087_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1, v___x_1086_);
v___y_1061_ = v___x_1087_;
goto v___jp_1060_;
}
else
{
lean_object* v___x_1088_; 
lean_dec(v_n_1057_);
v___x_1088_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__21));
v___y_1061_ = v___x_1088_;
goto v___jp_1060_;
}
v___jp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1059_);
lean_ctor_set(v___x_1062_, 1, v___y_1061_);
v___x_1063_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1066_ = l_Nat_reprFast(v_x_1056_);
v___x_1067_ = lean_string_append(v___x_1065_, v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1064_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_box(1);
v___x_1073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_1058_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
return v___x_1075_;
}
}
case 25:
{
lean_object* v_x_1089_; lean_object* v_n_1090_; lean_object* v_b_1091_; lean_object* v___x_1092_; lean_object* v___y_1094_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_x_1089_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_x_1089_);
v_n_1090_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_n_1090_);
v_b_1091_ = lean_ctor_get(v_a_922_, 2);
lean_inc(v_b_1091_);
lean_dec_ref_known(v_a_922_, 3);
v___x_1092_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_nat_dec_eq(v_n_1090_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1111_ = l_Nat_reprFast(v_n_1090_);
v___x_1112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
v___x_1113_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__20, &l_Lean_IR_formatFnBodyHead___closed__20_once, _init_l_Lean_IR_formatFnBodyHead___closed__20);
v___x_1114_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1112_);
v___x_1116_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_1117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1113_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = 0;
v___x_1120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*1, v___x_1119_);
v___y_1094_ = v___x_1120_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1121_; 
lean_dec(v_n_1090_);
v___x_1121_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__21));
v___y_1094_ = v___x_1121_;
goto v___jp_1093_;
}
v___jp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1092_);
lean_ctor_set(v___x_1095_, 1, v___y_1094_);
v___x_1096_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1099_ = l_Nat_reprFast(v_x_1089_);
v___x_1100_ = lean_string_append(v___x_1098_, v___x_1099_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1097_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = lean_box(1);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_1091_);
v___x_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
return v___x_1108_;
}
}
case 26:
{
lean_object* v_x_1122_; lean_object* v_b_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1141_; 
v_x_1122_ = lean_ctor_get(v_a_922_, 0);
v_b_1123_ = lean_ctor_get(v_a_922_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_a_922_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1125_ = v_a_922_;
v_isShared_1126_ = v_isSharedCheck_1141_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_b_1123_);
lean_inc(v_x_1122_);
lean_dec(v_a_922_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1141_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1127_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__25));
v___x_1128_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1129_ = l_Nat_reprFast(v_x_1122_);
v___x_1130_ = lean_string_append(v___x_1128_, v___x_1129_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 5);
lean_ctor_set(v___x_1125_, 1, v___x_1131_);
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1133_ = v___x_1125_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = lean_box(1);
v___x_1137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_1123_);
v___x_1139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
return v___x_1139_;
}
}
}
case 27:
{
lean_object* v_x_1142_; lean_object* v_xType_1143_; lean_object* v_cs_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_x_1142_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_x_1142_);
v_xType_1143_ = lean_ctor_get(v_a_922_, 2);
lean_inc(v_xType_1143_);
v_cs_1144_ = lean_ctor_get(v_a_922_, 3);
lean_inc_ref(v_cs_1144_);
lean_dec_ref_known(v_a_922_, 4);
v___x_1145_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__27));
v___x_1146_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1147_ = l_Nat_reprFast(v_x_1142_);
v___x_1148_ = lean_string_append(v___x_1146_, v___x_1147_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1145_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_xType_1143_);
v___x_1154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5));
v___x_1156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = lean_array_get_size(v_cs_1144_);
v___x_1160_ = lean_nat_dec_lt(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref(v_cs_1144_);
lean_dec(v_indent_921_);
v___x_1161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1156_);
lean_ctor_set(v___x_1161_, 1, v___x_1157_);
return v___x_1161_;
}
else
{
size_t v___x_1162_; size_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = ((size_t)0ULL);
v___x_1163_ = lean_usize_of_nat(v___x_1159_);
v___x_1164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_921_, v_cs_1144_, v___x_1162_, v___x_1163_, v___x_1157_);
lean_dec_ref(v_cs_1144_);
v___x_1165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1156_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
return v___x_1165_;
}
}
case 29:
{
lean_object* v_j_1166_; lean_object* v_ys_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_indent_921_);
v_j_1166_ = lean_ctor_get(v_a_922_, 0);
v_ys_1167_ = lean_ctor_get(v_a_922_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_a_922_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1169_ = v_a_922_;
v_isShared_1170_ = v_isSharedCheck_1181_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_ys_1167_);
lean_inc(v_j_1166_);
lean_dec(v_a_922_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1181_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1171_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__31));
v___x_1172_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__0));
v___x_1173_ = l_Nat_reprFast(v_j_1166_);
v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 5);
lean_ctor_set(v___x_1169_, 1, v___x_1175_);
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1177_ = v___x_1169_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1167_);
lean_dec_ref(v_ys_1167_);
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
return v___x_1179_;
}
}
}
case 28:
{
lean_object* v_x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v_indent_921_);
v_x_1182_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_x_1182_);
lean_dec_ref_known(v_a_922_, 1);
v___x_1183_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__33));
v___x_1184_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_1182_);
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
return v___x_1185_;
}
case 30:
{
lean_object* v___x_1186_; 
lean_dec(v_indent_921_);
v___x_1186_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__35));
return v___x_1186_;
}
default: 
{
lean_object* v_x_1187_; lean_object* v_ty_1188_; lean_object* v_b_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_x_1187_ = l_Lean_IR_FnBody_targetVar(v_a_922_);
v_ty_1188_ = l_Lean_IR_FnBody_targetType(v_a_922_);
v_b_1189_ = l_Lean_IR_FnBody_body(v_a_922_);
v___x_1190_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__40));
v___x_1191_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1192_ = l_Nat_reprFast(v_x_1187_);
v___x_1193_ = lean_string_append(v___x_1191_, v___x_1192_);
lean_dec_ref(v___x_1192_);
v___x_1194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1190_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1188_);
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_1201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_a_922_);
v___x_1203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_box(1);
v___x_1207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_921_, v_b_1189_);
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(lean_object* v_indent_1210_, lean_object* v_as_1211_, size_t v_i_1212_, size_t v_stop_1213_, lean_object* v_b_1214_){
_start:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_usize_dec_eq(v_i_1212_, v_stop_1213_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; 
v___x_1216_ = lean_array_uget_borrowed(v_as_1211_, v_i_1212_);
v___x_1217_ = lean_box(1);
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_b_1214_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
lean_inc_n(v_indent_1210_, 2);
v___x_1219_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop), 2, 1);
lean_closure_set(v___x_1219_, 0, v_indent_1210_);
lean_inc(v___x_1216_);
v___x_1220_ = l_Lean_IR_formatAlt(v___x_1219_, v_indent_1210_, v___x_1216_);
v___x_1221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1218_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1212_, v___x_1222_);
v_i_1212_ = v___x_1223_;
v_b_1214_ = v___x_1221_;
goto _start;
}
else
{
lean_dec(v_indent_1210_);
return v_b_1214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0___boxed(lean_object* v_indent_1225_, lean_object* v_as_1226_, lean_object* v_i_1227_, lean_object* v_stop_1228_, lean_object* v_b_1229_){
_start:
{
size_t v_i_boxed_1230_; size_t v_stop_boxed_1231_; lean_object* v_res_1232_; 
v_i_boxed_1230_ = lean_unbox_usize(v_i_1227_);
lean_dec(v_i_1227_);
v_stop_boxed_1231_ = lean_unbox_usize(v_stop_1228_);
lean_dec(v_stop_1228_);
v_res_1232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_1225_, v_as_1226_, v_i_boxed_1230_, v_stop_boxed_1231_, v_b_1229_);
lean_dec_ref(v_as_1226_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody(lean_object* v_fnBody_1233_, lean_object* v_indent_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_1234_, v_fnBody_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatFnBody___lam__0(lean_object* v_fnBody_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(2u);
v___x_1238_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_1237_, v_fnBody_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringFnBody___lam__0(lean_object* v_b_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1242_ = lean_unsigned_to_nat(2u);
v___x_1243_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_1242_, v_b_1241_);
v___x_1244_ = l_Std_Format_defWidth;
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = l_Std_Format_pretty(v___x_1243_, v___x_1244_, v___x_1245_, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatDecl(lean_object* v_decl_1255_, lean_object* v_indent_1256_){
_start:
{
if (lean_obj_tag(v_decl_1255_) == 0)
{
lean_object* v_f_1257_; lean_object* v_xs_1258_; lean_object* v_type_1259_; lean_object* v_body_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_f_1257_ = lean_ctor_get(v_decl_1255_, 0);
lean_inc(v_f_1257_);
v_xs_1258_ = lean_ctor_get(v_decl_1255_, 1);
lean_inc_ref(v_xs_1258_);
v_type_1259_ = lean_ctor_get(v_decl_1255_, 2);
lean_inc(v_type_1259_);
v_body_1260_ = lean_ctor_get(v_decl_1255_, 3);
lean_inc(v_body_1260_);
lean_dec_ref_known(v_decl_1255_, 5);
v___x_1261_ = ((lean_object*)(l_Lean_IR_formatDecl___closed__1));
v___x_1262_ = 1;
v___x_1263_ = l_Lean_Name_toString(v_f_1257_, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1261_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_1258_);
lean_dec_ref(v_xs_1258_);
v___x_1267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_1259_);
v___x_1271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
lean_inc(v_indent_1256_);
v___x_1274_ = lean_nat_to_int(v_indent_1256_);
v___x_1275_ = lean_box(1);
v___x_1276_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_1256_, v_body_1260_);
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1274_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1273_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
return v___x_1279_;
}
else
{
lean_object* v_f_1280_; lean_object* v_xs_1281_; lean_object* v_type_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec(v_indent_1256_);
v_f_1280_ = lean_ctor_get(v_decl_1255_, 0);
lean_inc(v_f_1280_);
v_xs_1281_ = lean_ctor_get(v_decl_1255_, 1);
lean_inc_ref(v_xs_1281_);
v_type_1282_ = lean_ctor_get(v_decl_1255_, 2);
lean_inc(v_type_1282_);
lean_dec_ref_known(v_decl_1255_, 4);
v___x_1283_ = ((lean_object*)(l_Lean_IR_formatDecl___closed__3));
v___x_1284_ = 1;
v___x_1285_ = l_Lean_Name_toString(v_f_1280_, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1283_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_1281_);
lean_dec_ref(v_xs_1281_);
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_1282_);
v___x_1293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatDecl___lam__0(lean_object* v_decl_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(2u);
v___x_1296_ = l_Lean_IR_formatDecl(v_decl_1294_, v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declToString(lean_object* v_d_1299_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1300_ = lean_unsigned_to_nat(2u);
v___x_1301_ = l_Lean_IR_formatDecl(v_d_1299_, v___x_1300_);
v___x_1302_ = l_Std_Format_defWidth;
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = l_Std_Format_pretty(v___x_1301_, v___x_1302_, v___x_1303_, v___x_1303_);
return v___x_1304_;
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
