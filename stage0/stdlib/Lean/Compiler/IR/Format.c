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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v_name_106_; lean_object* v_cidx_107_; lean_object* v_usize_108_; lean_object* v_ssize_109_; lean_object* v_r_111_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_r_125_; lean_object* v___x_136_; uint8_t v___x_137_; 
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
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_nat_dec_lt(v___x_136_, v_usize_108_);
if (v___x_137_ == 0)
{
uint8_t v___x_138_; 
v___x_138_ = lean_nat_dec_lt(v___x_136_, v_ssize_109_);
if (v___x_138_ == 0)
{
lean_dec(v_ssize_109_);
lean_dec(v_usize_108_);
v_r_111_ = v_r_125_;
goto v___jp_110_;
}
else
{
goto v___jp_126_;
}
}
else
{
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
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_r_135_; 
v___x_127_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7));
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v_r_125_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = l_Nat_reprFast(v_usize_108_);
v___x_130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_128_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_127_);
v___x_133_ = l_Nat_reprFast(v_ssize_109_);
v___x_134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
v_r_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_r_135_, 0, v___x_132_);
lean_ctor_set(v_r_135_, 1, v___x_134_);
v_r_111_ = v_r_135_;
goto v___jp_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatCtorInfo___private__1(lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_a_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__1(lean_object* v_msg_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_box(0);
v___x_145_ = lean_panic_fn_borrowed(v___x_144_, v_msg_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(lean_object* v_as_146_, size_t v_i_147_, size_t v_stop_148_, lean_object* v_b_149_){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = lean_usize_dec_eq(v_i_147_, v_stop_148_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; size_t v___x_156_; size_t v___x_157_; 
v___x_151_ = lean_array_uget_borrowed(v_as_146_, v_i_147_);
v___x_152_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v_b_149_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
lean_inc(v___x_151_);
v___x_154_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v___x_151_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_add(v_i_147_, v___x_156_);
v_i_147_ = v___x_157_;
v_b_149_ = v___x_155_;
goto _start;
}
else
{
return v_b_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0___boxed(lean_object* v_as_159_, lean_object* v_i_160_, lean_object* v_stop_161_, lean_object* v_b_162_){
_start:
{
size_t v_i_boxed_163_; size_t v_stop_boxed_164_; lean_object* v_res_165_; 
v_i_boxed_163_ = lean_unbox_usize(v_i_160_);
lean_dec(v_i_160_);
v_stop_boxed_164_ = lean_unbox_usize(v_stop_161_);
lean_dec(v_stop_161_);
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_as_159_, v_i_boxed_163_, v_stop_boxed_164_, v_b_162_);
lean_dec_ref(v_as_159_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(lean_object* v_args_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_167_ = lean_box(0);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_array_get_size(v_args_166_);
v___x_170_ = lean_nat_dec_lt(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
return v___x_167_;
}
else
{
size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; 
v___x_171_ = ((size_t)0ULL);
v___x_172_ = lean_usize_of_nat(v___x_169_);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_166_, v___x_171_, v___x_172_, v___x_167_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(lean_object* v_args_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_args_174_);
lean_dec_ref(v_args_174_);
return v_res_175_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__30));
v___x_221_ = lean_unsigned_to_nat(9u);
v___x_222_ = lean_unsigned_to_nat(63u);
v___x_223_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__29));
v___x_224_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__28));
v___x_225_ = l_mkPanicMessageWithDecl(v___x_224_, v___x_223_, v___x_222_, v___x_221_, v___x_220_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(lean_object* v_x_226_){
_start:
{
uint64_t v_v_228_; 
switch(lean_obj_tag(v_x_226_))
{
case 0:
{
lean_object* v_i_232_; lean_object* v_ys_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_i_232_ = lean_ctor_get(v_x_226_, 2);
lean_inc_ref(v_i_232_);
v_ys_233_ = lean_ctor_get(v_x_226_, 3);
lean_inc_ref(v_ys_233_);
lean_dec_ref_known(v_x_226_, 4);
v___x_234_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_232_);
v___x_235_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_233_);
lean_dec_ref(v_ys_233_);
v___x_236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
return v___x_236_;
}
case 1:
{
lean_object* v_n_237_; lean_object* v_x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_n_237_ = lean_ctor_get(v_x_226_, 2);
lean_inc(v_n_237_);
v_x_238_ = lean_ctor_get(v_x_226_, 3);
lean_inc(v_x_238_);
lean_dec_ref_known(v_x_226_, 4);
v___x_239_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1));
v___x_240_ = l_Nat_reprFast(v_n_237_);
v___x_241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_246_ = l_Nat_reprFast(v_x_238_);
v___x_247_ = lean_string_append(v___x_245_, v___x_246_);
lean_dec_ref(v___x_246_);
v___x_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_244_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
case 2:
{
lean_object* v_x_250_; lean_object* v_i_251_; uint8_t v_updtHeader_252_; lean_object* v_ys_253_; lean_object* v___x_254_; lean_object* v___y_256_; 
v_x_250_ = lean_ctor_get(v_x_226_, 2);
lean_inc(v_x_250_);
v_i_251_ = lean_ctor_get(v_x_226_, 3);
lean_inc_ref(v_i_251_);
v_updtHeader_252_ = lean_ctor_get_uint8(v_x_226_, sizeof(void*)*5);
v_ys_253_ = lean_ctor_get(v_x_226_, 4);
lean_inc_ref(v_ys_253_);
lean_dec_ref_known(v_x_226_, 5);
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
lean_inc_ref(v___y_256_);
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
lean_object* v_i_274_; lean_object* v_x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_i_274_ = lean_ctor_get(v_x_226_, 2);
lean_inc(v_i_274_);
v_x_275_ = lean_ctor_get(v_x_226_, 3);
lean_inc(v_x_275_);
lean_dec_ref_known(v_x_226_, 4);
v___x_276_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11));
v___x_277_ = l_Nat_reprFast(v_i_274_);
v___x_278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___x_279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_283_ = l_Nat_reprFast(v_x_275_);
v___x_284_ = lean_string_append(v___x_282_, v___x_283_);
lean_dec_ref(v___x_283_);
v___x_285_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_281_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
return v___x_286_;
}
case 4:
{
lean_object* v_i_287_; lean_object* v_x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_i_287_ = lean_ctor_get(v_x_226_, 2);
lean_inc(v_i_287_);
v_x_288_ = lean_ctor_get(v_x_226_, 3);
lean_inc(v_x_288_);
lean_dec_ref_known(v_x_226_, 4);
v___x_289_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13));
v___x_290_ = l_Nat_reprFast(v_i_287_);
v___x_291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_296_ = l_Nat_reprFast(v_x_288_);
v___x_297_ = lean_string_append(v___x_295_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_294_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
case 5:
{
lean_object* v_n_300_; lean_object* v_offset_301_; lean_object* v_x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_n_300_ = lean_ctor_get(v_x_226_, 3);
lean_inc(v_n_300_);
v_offset_301_ = lean_ctor_get(v_x_226_, 4);
lean_inc(v_offset_301_);
v_x_302_ = lean_ctor_get(v_x_226_, 5);
lean_inc(v_x_302_);
lean_dec_ref_known(v_x_226_, 6);
v___x_303_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15));
v___x_304_ = l_Nat_reprFast(v_n_300_);
v___x_305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = l_Nat_reprFast(v_offset_301_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_308_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3));
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_315_ = l_Nat_reprFast(v_x_302_);
v___x_316_ = lean_string_append(v___x_314_, v___x_315_);
lean_dec_ref(v___x_315_);
v___x_317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_313_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
return v___x_318_;
}
case 6:
{
lean_object* v_c_319_; lean_object* v_ys_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_c_319_ = lean_ctor_get(v_x_226_, 3);
lean_inc(v_c_319_);
v_ys_320_ = lean_ctor_get(v_x_226_, 4);
lean_inc_ref(v_ys_320_);
lean_dec_ref_known(v_x_226_, 5);
v___x_321_ = 1;
v___x_322_ = l_Lean_Name_toString(v_c_319_, v___x_321_);
v___x_323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
v___x_324_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_320_);
lean_dec_ref(v_ys_320_);
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
return v___x_325_;
}
case 7:
{
lean_object* v_c_326_; lean_object* v_ys_327_; lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_c_326_ = lean_ctor_get(v_x_226_, 2);
lean_inc(v_c_326_);
v_ys_327_ = lean_ctor_get(v_x_226_, 3);
lean_inc_ref(v_ys_327_);
lean_dec_ref_known(v_x_226_, 4);
v___x_328_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19));
v___x_329_ = 1;
v___x_330_ = l_Lean_Name_toString(v_c_326_, v___x_329_);
v___x_331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___x_332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_328_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_327_);
lean_dec_ref(v_ys_327_);
v___x_334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
return v___x_334_;
}
case 8:
{
lean_object* v_x_335_; lean_object* v_ys_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_x_335_ = lean_ctor_get(v_x_226_, 2);
lean_inc(v_x_335_);
v_ys_336_ = lean_ctor_get(v_x_226_, 3);
lean_inc_ref(v_ys_336_);
lean_dec_ref_known(v_x_226_, 4);
v___x_337_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21));
v___x_338_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_339_ = l_Nat_reprFast(v_x_335_);
v___x_340_ = lean_string_append(v___x_338_, v___x_339_);
lean_dec_ref(v___x_339_);
v___x_341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_337_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_336_);
lean_dec_ref(v_ys_336_);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
return v___x_344_;
}
case 9:
{
lean_object* v_x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_x_345_ = lean_ctor_get(v_x_226_, 3);
lean_inc(v_x_345_);
lean_dec_ref_known(v_x_226_, 4);
v___x_346_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23));
v___x_347_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_348_ = l_Nat_reprFast(v_x_345_);
v___x_349_ = lean_string_append(v___x_347_, v___x_348_);
lean_dec_ref(v___x_348_);
v___x_350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
v___x_351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_346_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
return v___x_351_;
}
case 10:
{
lean_object* v_x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_x_352_ = lean_ctor_get(v_x_226_, 3);
lean_inc(v_x_352_);
lean_dec_ref_known(v_x_226_, 4);
v___x_353_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25));
v___x_354_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_355_ = l_Nat_reprFast(v_x_352_);
v___x_356_ = lean_string_append(v___x_354_, v___x_355_);
lean_dec_ref(v___x_355_);
v___x_357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_353_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
return v___x_358_;
}
case 11:
{
uint8_t v_v_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_v_359_ = lean_ctor_get_uint8(v_x_226_, sizeof(void*)*2);
lean_dec_ref_known(v_x_226_, 2);
v___x_360_ = lean_uint8_to_nat(v_v_359_);
v___x_361_ = l_Nat_reprFast(v___x_360_);
v___x_362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
case 12:
{
uint16_t v_v_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_v_363_ = lean_ctor_get_uint16(v_x_226_, sizeof(void*)*2);
lean_dec_ref_known(v_x_226_, 2);
v___x_364_ = lean_uint16_to_nat(v_v_363_);
v___x_365_ = l_Nat_reprFast(v___x_364_);
v___x_366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
case 13:
{
uint32_t v_v_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_v_367_ = lean_ctor_get_uint32(v_x_226_, sizeof(void*)*2);
lean_dec_ref_known(v_x_226_, 2);
v___x_368_ = lean_uint32_to_nat(v_v_367_);
v___x_369_ = l_Nat_reprFast(v___x_368_);
v___x_370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
case 14:
{
uint64_t v_v_371_; 
v_v_371_ = lean_ctor_get_uint64(v_x_226_, sizeof(void*)*2);
lean_dec_ref_known(v_x_226_, 2);
v_v_228_ = v_v_371_;
goto v___jp_227_;
}
case 15:
{
uint64_t v_v_372_; 
v_v_372_ = lean_ctor_get_uint64(v_x_226_, sizeof(void*)*2);
lean_dec_ref_known(v_x_226_, 2);
v_v_228_ = v_v_372_;
goto v___jp_227_;
}
case 16:
{
lean_object* v_v_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_v_373_ = lean_ctor_get(v_x_226_, 2);
lean_inc(v_v_373_);
lean_dec_ref_known(v_x_226_, 3);
v___x_374_ = l_Nat_reprFast(v_v_373_);
v___x_375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
case 17:
{
lean_object* v_v_376_; lean_object* v___x_377_; 
v_v_376_ = lean_ctor_get(v_x_226_, 2);
lean_inc_ref(v_v_376_);
lean_dec_ref_known(v_x_226_, 3);
v___x_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_377_, 0, v_v_376_);
return v___x_377_;
}
case 18:
{
lean_object* v_x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_x_378_ = lean_ctor_get(v_x_226_, 2);
lean_inc(v_x_378_);
lean_dec_ref_known(v_x_226_, 3);
v___x_379_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27));
v___x_380_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_381_ = l_Nat_reprFast(v_x_378_);
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
lean_dec_ref(v___x_381_);
v___x_383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_379_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
default: 
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_x_226_);
v___x_385_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__31);
v___x_386_ = l_panic___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__1(v___x_385_);
return v___x_386_;
}
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_uint64_to_nat(v_v_228_);
v___x_230_ = l_Nat_reprFast(v___x_229_);
v___x_231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__1(lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_nat_to_int(v_a_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v___x_421_; 
lean_dec(v_x_420_);
v___x_421_ = lean_box(0);
return v___x_421_;
}
else
{
lean_object* v_tail_422_; 
v_tail_422_ = lean_ctor_get(v_x_419_, 1);
if (lean_obj_tag(v_tail_422_) == 0)
{
lean_object* v_head_423_; lean_object* v___x_424_; 
lean_dec(v_x_420_);
v_head_423_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_head_423_);
lean_dec_ref_known(v_x_419_, 2);
v___x_424_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_423_);
return v___x_424_;
}
else
{
lean_object* v_head_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_inc(v_tail_422_);
v_head_425_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_head_425_);
lean_dec_ref_known(v_x_419_, 2);
v___x_426_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_425_);
v___x_427_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(v_x_420_, v___x_426_, v_tail_422_);
return v___x_427_;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20));
v___x_430_ = lean_string_length(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22);
v___x_432_ = lean_nat_to_int(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object* v_x_447_){
_start:
{
switch(lean_obj_tag(v_x_447_))
{
case 0:
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1));
return v___x_448_;
}
case 1:
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3));
return v___x_449_;
}
case 2:
{
lean_object* v___x_450_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5));
return v___x_450_;
}
case 3:
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7));
return v___x_451_;
}
case 4:
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9));
return v___x_452_;
}
case 5:
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11));
return v___x_453_;
}
case 6:
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2));
return v___x_454_;
}
case 7:
{
lean_object* v___x_455_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13));
return v___x_455_;
}
case 8:
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15));
return v___x_456_;
}
case 9:
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17));
return v___x_457_;
}
case 10:
{
lean_object* v_types_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_477_; 
v_types_458_ = lean_ctor_get(v_x_447_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_x_447_, 0);
lean_dec(v_unused_478_);
v___x_460_ = v_x_447_;
v_isShared_461_ = v_isSharedCheck_477_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_types_458_);
lean_dec(v_x_447_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_477_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19));
v___x_463_ = lean_array_to_list(v_types_458_);
v___x_464_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_465_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_463_, v___x_464_);
v___x_466_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
v___x_467_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24));
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 5);
lean_ctor_set(v___x_460_, 1, v___x_465_);
lean_ctor_set(v___x_460_, 0, v___x_467_);
v___x_469_ = v___x_460_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_465_);
v___x_469_ = v_reuseFailAlloc_476_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25));
v___x_471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_466_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = 0;
v___x_474_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*1, v___x_473_);
v___x_475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_462_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
return v___x_475_;
}
}
}
case 11:
{
lean_object* v_types_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_498_; 
v_types_479_ = lean_ctor_get(v_x_447_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v_x_447_, 0);
lean_dec(v_unused_499_);
v___x_481_ = v_x_447_;
v_isShared_482_ = v_isSharedCheck_498_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_types_479_);
lean_dec(v_x_447_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_498_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27));
v___x_484_ = lean_array_to_list(v_types_479_);
v___x_485_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_486_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_484_, v___x_485_);
v___x_487_ = lean_obj_once(&l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23, &l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once, _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
v___x_488_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24));
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 5);
lean_ctor_set(v___x_481_, 1, v___x_486_);
lean_ctor_set(v___x_481_, 0, v___x_488_);
v___x_490_ = v___x_481_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_486_);
v___x_490_ = v_reuseFailAlloc_497_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_491_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25));
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_487_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = 0;
v___x_495_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*1, v___x_494_);
v___x_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_483_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
return v___x_496_;
}
}
}
case 12:
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29));
return v___x_500_;
}
default: 
{
lean_object* v___x_501_; 
v___x_501_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31));
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_dec(v_x_502_);
return v_x_503_;
}
else
{
lean_object* v_head_505_; lean_object* v_tail_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v_head_505_ = lean_ctor_get(v_x_504_, 0);
v_tail_506_ = lean_ctor_get(v_x_504_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_516_ == 0)
{
v___x_508_ = v_x_504_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_tail_506_);
lean_inc(v_head_505_);
lean_dec(v_x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
lean_inc(v_x_502_);
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 5);
lean_ctor_set(v___x_508_, 1, v_x_502_);
lean_ctor_set(v___x_508_, 0, v_x_503_);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_x_503_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_x_502_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_505_);
v___x_513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v_x_503_ = v___x_513_;
v_x_504_ = v_tail_506_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatIRType___private__1(lean_object* v_a_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringIRType___lam__0(lean_object* v_f_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = l_Std_Format_defWidth;
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = l_Std_Format_pretty(v_f_521_, v___x_522_, v___x_523_, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(lean_object* v_x_540_){
_start:
{
lean_object* v_x_541_; uint8_t v_borrow_542_; lean_object* v_ty_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___y_553_; 
v_x_541_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_x_541_);
v_borrow_542_ = lean_ctor_get_uint8(v_x_540_, sizeof(void*)*2);
v_ty_543_ = lean_ctor_get(v_x_540_, 1);
lean_inc(v_ty_543_);
lean_dec_ref(v_x_540_);
v___x_544_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1));
v___x_545_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_546_ = l_Nat_reprFast(v_x_541_);
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_544_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
if (v_borrow_542_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8));
v___y_553_ = v___x_560_;
goto v___jp_552_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6));
v___y_553_ = v___x_561_;
goto v___jp_552_;
}
v___jp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
lean_inc_ref(v___y_553_);
v___x_554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_554_, 0, v___y_553_);
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_543_);
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5));
v___x_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatParam___private__1(lean_object* v_a_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v_a_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatAlt(lean_object* v_fmt_572_, lean_object* v_indent_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
lean_object* v_info_575_; lean_object* v_b_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_594_; 
v_info_575_ = lean_ctor_get(v_x_574_, 0);
v_b_576_ = lean_ctor_get(v_x_574_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_574_);
if (v_isSharedCheck_594_ == 0)
{
v___x_578_ = v_x_574_;
v_isShared_579_ = v_isSharedCheck_594_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_b_576_);
lean_inc(v_info_575_);
lean_dec(v_x_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_594_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_name_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_name_580_ = lean_ctor_get(v_info_575_, 0);
lean_inc(v_name_580_);
lean_dec_ref(v_info_575_);
v___x_581_ = 1;
v___x_582_ = l_Lean_Name_toString(v_name_580_, v___x_581_);
v___x_583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
v___x_584_ = ((lean_object*)(l_Lean_IR_formatAlt___closed__1));
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 5);
lean_ctor_set(v___x_578_, 1, v___x_584_);
lean_ctor_set(v___x_578_, 0, v___x_583_);
v___x_586_ = v___x_578_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_593_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_587_ = lean_nat_to_int(v_indent_573_);
v___x_588_ = lean_box(1);
v___x_589_ = lean_apply_1(v_fmt_572_, v_b_576_);
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_587_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_586_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
return v___x_592_;
}
}
}
else
{
lean_object* v_b_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_b_595_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_b_595_);
lean_dec_ref_known(v_x_574_, 1);
v___x_596_ = ((lean_object*)(l_Lean_IR_formatAlt___closed__3));
v___x_597_ = lean_nat_to_int(v_indent_573_);
v___x_598_ = lean_box(1);
v___x_599_ = lean_apply_1(v_fmt_572_, v_b_595_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_597_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_596_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(lean_object* v_as_603_, size_t v_i_604_, size_t v_stop_605_, lean_object* v_b_606_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = lean_usize_dec_eq(v_i_604_, v_stop_605_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; size_t v___x_613_; size_t v___x_614_; 
v___x_608_ = lean_array_uget_borrowed(v_as_603_, v_i_604_);
v___x_609_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v_b_606_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
lean_inc(v___x_608_);
v___x_611_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v___x_608_);
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_604_, v___x_613_);
v_i_604_ = v___x_614_;
v_b_606_ = v___x_612_;
goto _start;
}
else
{
return v_b_606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0___boxed(lean_object* v_as_616_, lean_object* v_i_617_, lean_object* v_stop_618_, lean_object* v_b_619_){
_start:
{
size_t v_i_boxed_620_; size_t v_stop_boxed_621_; lean_object* v_res_622_; 
v_i_boxed_620_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_stop_boxed_621_ = lean_unbox_usize(v_stop_618_);
lean_dec(v_stop_618_);
v_res_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_as_616_, v_i_boxed_620_, v_stop_boxed_621_, v_b_619_);
lean_dec_ref(v_as_616_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(lean_object* v_args_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_624_ = lean_box(0);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_array_get_size(v_args_623_);
v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
return v___x_624_;
}
else
{
size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v___x_628_ = ((size_t)0ULL);
v___x_629_ = lean_usize_of_nat(v___x_626_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_623_, v___x_628_, v___x_629_, v___x_624_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0___boxed(lean_object* v_args_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_args_631_);
lean_dec_ref(v_args_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams(lean_object* v_ps_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_ps_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams___boxed(lean_object* v_ps_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_IR_formatParams(v_ps_635_);
lean_dec_ref(v_ps_635_);
return v_res_636_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__19(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0));
v___x_666_ = lean_string_length(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__20(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__19, &l_Lean_IR_formatFnBodyHead___closed__19_once, _init_l_Lean_IR_formatFnBodyHead___closed__19);
v___x_668_ = lean_nat_to_int(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__38(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_694_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__37));
v___x_695_ = lean_unsigned_to_nat(4u);
v___x_696_ = lean_unsigned_to_nat(114u);
v___x_697_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__36));
v___x_698_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__28));
v___x_699_ = l_mkPanicMessageWithDecl(v___x_698_, v___x_697_, v___x_696_, v___x_695_, v___x_694_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBodyHead(lean_object* v_x_703_){
_start:
{
switch(lean_obj_tag(v_x_703_))
{
case 19:
{
lean_object* v_j_704_; lean_object* v_xs_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_j_704_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_j_704_);
v_xs_705_ = lean_ctor_get(v_x_703_, 1);
lean_inc_ref(v_xs_705_);
lean_dec_ref_known(v_x_703_, 4);
v___x_706_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__0));
v___x_707_ = l_Nat_reprFast(v_j_704_);
v___x_708_ = lean_string_append(v___x_706_, v___x_707_);
lean_dec_ref(v___x_707_);
v___x_709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
v___x_710_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_705_);
lean_dec_ref(v_xs_705_);
v___x_711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__2));
v___x_713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
return v___x_713_;
}
case 20:
{
lean_object* v_x_714_; lean_object* v_i_715_; lean_object* v_y_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_x_714_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_x_714_);
v_i_715_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_i_715_);
v_y_716_ = lean_ctor_get(v_x_703_, 2);
lean_inc(v_y_716_);
lean_dec_ref_known(v_x_703_, 4);
v___x_717_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_718_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_719_ = l_Nat_reprFast(v_x_714_);
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_717_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = l_Nat_reprFast(v_i_715_);
v___x_726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_724_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_716_);
v___x_731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
return v___x_731_;
}
case 22:
{
lean_object* v_x_732_; lean_object* v_i_733_; lean_object* v_y_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_x_732_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_x_732_);
v_i_733_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_i_733_);
v_y_734_ = lean_ctor_get(v_x_703_, 2);
lean_inc(v_y_734_);
lean_dec_ref_known(v_x_703_, 4);
v___x_735_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__8));
v___x_736_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_737_ = l_Nat_reprFast(v_x_732_);
v___x_738_ = lean_string_append(v___x_736_, v___x_737_);
lean_dec_ref(v___x_737_);
v___x_739_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
v___x_740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_735_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Nat_reprFast(v_i_733_);
v___x_744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_742_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Nat_reprFast(v_y_734_);
v___x_749_ = lean_string_append(v___x_736_, v___x_748_);
lean_dec_ref(v___x_748_);
v___x_750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
v___x_751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_747_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
return v___x_751_;
}
case 23:
{
lean_object* v_x_752_; lean_object* v_i_753_; lean_object* v_offset_754_; lean_object* v_y_755_; lean_object* v_ty_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_x_752_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_x_752_);
v_i_753_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_i_753_);
v_offset_754_ = lean_ctor_get(v_x_703_, 2);
lean_inc(v_offset_754_);
v_y_755_ = lean_ctor_get(v_x_703_, 3);
lean_inc(v_y_755_);
v_ty_756_ = lean_ctor_get(v_x_703_, 4);
lean_inc(v_ty_756_);
lean_dec_ref_known(v_x_703_, 6);
v___x_757_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_758_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_759_ = l_Nat_reprFast(v_x_752_);
v___x_760_ = lean_string_append(v___x_758_, v___x_759_);
lean_dec_ref(v___x_759_);
v___x_761_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v___x_762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_757_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Nat_reprFast(v_i_753_);
v___x_766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v___x_767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_764_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Nat_reprFast(v_offset_754_);
v___x_771_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
v___x_772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_769_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__12));
v___x_774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_756_);
v___x_776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Nat_reprFast(v_y_755_);
v___x_780_ = lean_string_append(v___x_758_, v___x_779_);
lean_dec_ref(v___x_779_);
v___x_781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_778_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
return v___x_782_;
}
case 21:
{
lean_object* v_x_783_; lean_object* v_cidx_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_x_783_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_x_783_);
v_cidx_784_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_cidx_784_);
lean_dec_ref_known(v_x_703_, 3);
v___x_785_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__16));
v___x_786_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_787_ = l_Nat_reprFast(v_x_783_);
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
lean_dec_ref(v___x_787_);
v___x_789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___x_790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_785_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Nat_reprFast(v_cidx_784_);
v___x_794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
v___x_795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_792_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
return v___x_795_;
}
case 24:
{
lean_object* v_x_796_; lean_object* v_n_797_; lean_object* v___x_798_; lean_object* v___y_800_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_x_796_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_x_796_);
v_n_797_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_n_797_);
lean_dec_ref_known(v_x_703_, 3);
v___x_798_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__18));
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_dec_eq(v_n_797_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; 
v___x_811_ = l_Nat_reprFast(v_n_797_);
v___x_812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__20, &l_Lean_IR_formatFnBodyHead___closed__20_once, _init_l_Lean_IR_formatFnBodyHead___closed__20);
v___x_814_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_812_);
v___x_816_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_813_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = 0;
v___x_820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*1, v___x_819_);
v___y_800_ = v___x_820_;
goto v___jp_799_;
}
else
{
lean_object* v___x_821_; 
lean_dec(v_n_797_);
v___x_821_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__21));
v___y_800_ = v___x_821_;
goto v___jp_799_;
}
v___jp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_798_);
lean_ctor_set(v___x_801_, 1, v___y_800_);
v___x_802_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_805_ = l_Nat_reprFast(v_x_796_);
v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
lean_dec_ref(v___x_805_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_803_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
return v___x_808_;
}
}
case 25:
{
lean_object* v_x_822_; lean_object* v_n_823_; lean_object* v___x_824_; lean_object* v___y_826_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_x_822_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_x_822_);
v_n_823_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_n_823_);
lean_dec_ref_known(v_x_703_, 3);
v___x_824_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_dec_eq(v_n_823_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; 
v___x_837_ = l_Nat_reprFast(v_n_823_);
v___x_838_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__20, &l_Lean_IR_formatFnBodyHead___closed__20_once, _init_l_Lean_IR_formatFnBodyHead___closed__20);
v___x_840_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v___x_838_);
v___x_842_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_839_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = 0;
v___x_846_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*1, v___x_845_);
v___y_826_ = v___x_846_;
goto v___jp_825_;
}
else
{
lean_object* v___x_847_; 
lean_dec(v_n_823_);
v___x_847_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__21));
v___y_826_ = v___x_847_;
goto v___jp_825_;
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_827_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_824_);
lean_ctor_set(v___x_827_, 1, v___y_826_);
v___x_828_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_831_ = l_Nat_reprFast(v_x_822_);
v___x_832_ = lean_string_append(v___x_830_, v___x_831_);
lean_dec_ref(v___x_831_);
v___x_833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_829_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
return v___x_834_;
}
}
case 26:
{
lean_object* v_x_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_860_; 
v_x_848_ = lean_ctor_get(v_x_703_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_x_703_, 1);
lean_dec(v_unused_861_);
v___x_850_ = v_x_703_;
v_isShared_851_ = v_isSharedCheck_860_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_x_848_);
lean_dec(v_x_703_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_860_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_852_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__25));
v___x_853_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_854_ = l_Nat_reprFast(v_x_848_);
v___x_855_ = lean_string_append(v___x_853_, v___x_854_);
lean_dec_ref(v___x_854_);
v___x_856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 5);
lean_ctor_set(v___x_850_, 1, v___x_856_);
lean_ctor_set(v___x_850_, 0, v___x_852_);
v___x_858_ = v___x_850_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
case 27:
{
lean_object* v_x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_x_862_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_x_862_);
lean_dec_ref_known(v_x_703_, 4);
v___x_863_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__27));
v___x_864_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_865_ = l_Nat_reprFast(v_x_862_);
v___x_866_ = lean_string_append(v___x_864_, v___x_865_);
lean_dec_ref(v___x_865_);
v___x_867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_863_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__29));
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
return v___x_870_;
}
case 29:
{
lean_object* v_j_871_; lean_object* v_ys_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_886_; 
v_j_871_ = lean_ctor_get(v_x_703_, 0);
v_ys_872_ = lean_ctor_get(v_x_703_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_886_ == 0)
{
v___x_874_ = v_x_703_;
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_ys_872_);
lean_inc(v_j_871_);
lean_dec(v_x_703_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_876_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__31));
v___x_877_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__0));
v___x_878_ = l_Nat_reprFast(v_j_871_);
v___x_879_ = lean_string_append(v___x_877_, v___x_878_);
lean_dec_ref(v___x_878_);
v___x_880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 5);
lean_ctor_set(v___x_874_, 1, v___x_880_);
lean_ctor_set(v___x_874_, 0, v___x_876_);
v___x_882_ = v___x_874_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_880_);
v___x_882_ = v_reuseFailAlloc_885_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_872_);
lean_dec_ref(v_ys_872_);
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
return v___x_884_;
}
}
}
case 28:
{
lean_object* v_x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_x_887_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_x_887_);
lean_dec_ref_known(v_x_703_, 1);
v___x_888_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__33));
v___x_889_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_887_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
return v___x_890_;
}
case 30:
{
lean_object* v___x_891_; 
v___x_891_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__35));
return v___x_891_;
}
default: 
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_IR_FnBody_isVarDecl(v_x_703_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v_x_703_);
v___x_893_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__38, &l_Lean_IR_formatFnBodyHead___closed__38_once, _init_l_Lean_IR_formatFnBodyHead___closed__38);
v___x_894_ = l_panic___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__1(v___x_893_);
return v___x_894_;
}
else
{
lean_object* v_x_895_; lean_object* v_ty_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_x_895_ = l_Lean_IR_FnBody_targetVar(v_x_703_);
v_ty_896_ = l_Lean_IR_FnBody_targetType(v_x_703_);
v___x_897_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__40));
v___x_898_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_899_ = l_Nat_reprFast(v_x_895_);
v___x_900_ = lean_string_append(v___x_898_, v___x_899_);
lean_dec_ref(v___x_899_);
v___x_901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_897_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_896_);
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_x_703_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_format_fn_body_head(lean_object* v_fn_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_912_ = l_Lean_IR_formatFnBodyHead(v_fn_911_);
v___x_913_ = l_Std_Format_defWidth;
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = l_Std_Format_pretty(v___x_912_, v___x_913_, v___x_914_, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(lean_object* v_indent_925_, lean_object* v_a_926_){
_start:
{
switch(lean_obj_tag(v_a_926_))
{
case 19:
{
lean_object* v_j_927_; lean_object* v_xs_928_; lean_object* v_v_929_; lean_object* v_b_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_j_927_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_j_927_);
v_xs_928_ = lean_ctor_get(v_a_926_, 1);
lean_inc_ref(v_xs_928_);
v_v_929_ = lean_ctor_get(v_a_926_, 2);
lean_inc(v_v_929_);
v_b_930_ = lean_ctor_get(v_a_926_, 3);
lean_inc(v_b_930_);
lean_dec_ref_known(v_a_926_, 4);
v___x_931_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__0));
v___x_932_ = l_Nat_reprFast(v_j_927_);
v___x_933_ = lean_string_append(v___x_931_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___x_935_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_928_);
lean_dec_ref(v_xs_928_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
lean_inc_n(v_indent_925_, 2);
v___x_939_ = lean_nat_to_int(v_indent_925_);
v___x_940_ = lean_box(1);
v___x_941_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_v_929_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_939_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_938_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_940_);
v___x_948_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_930_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
return v___x_949_;
}
case 20:
{
lean_object* v_x_950_; lean_object* v_i_951_; lean_object* v_y_952_; lean_object* v_b_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_x_950_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_x_950_);
v_i_951_ = lean_ctor_get(v_a_926_, 1);
lean_inc(v_i_951_);
v_y_952_ = lean_ctor_get(v_a_926_, 2);
lean_inc(v_y_952_);
v_b_953_ = lean_ctor_get(v_a_926_, 3);
lean_inc(v_b_953_);
lean_dec_ref_known(v_a_926_, 4);
v___x_954_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__4));
v___x_955_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_956_ = l_Nat_reprFast(v_x_950_);
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
lean_dec_ref(v___x_956_);
v___x_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_954_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l_Nat_reprFast(v_i_951_);
v___x_963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_961_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_952_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_box(1);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_953_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
return v___x_974_;
}
case 22:
{
lean_object* v_x_975_; lean_object* v_i_976_; lean_object* v_y_977_; lean_object* v_b_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_x_975_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_x_975_);
v_i_976_ = lean_ctor_get(v_a_926_, 1);
lean_inc(v_i_976_);
v_y_977_ = lean_ctor_get(v_a_926_, 2);
lean_inc(v_y_977_);
v_b_978_ = lean_ctor_get(v_a_926_, 3);
lean_inc(v_b_978_);
lean_dec_ref_known(v_a_926_, 4);
v___x_979_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__8));
v___x_980_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_981_ = l_Nat_reprFast(v_x_975_);
v___x_982_ = lean_string_append(v___x_980_, v___x_981_);
lean_dec_ref(v___x_981_);
v___x_983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_979_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Nat_reprFast(v_i_976_);
v___x_988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_986_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__6));
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Nat_reprFast(v_y_977_);
v___x_993_ = lean_string_append(v___x_980_, v___x_992_);
lean_dec_ref(v___x_992_);
v___x_994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_991_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_box(1);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_978_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
return v___x_1001_;
}
case 23:
{
lean_object* v_x_1002_; lean_object* v_i_1003_; lean_object* v_offset_1004_; lean_object* v_y_1005_; lean_object* v_ty_1006_; lean_object* v_b_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_x_1002_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_x_1002_);
v_i_1003_ = lean_ctor_get(v_a_926_, 1);
lean_inc(v_i_1003_);
v_offset_1004_ = lean_ctor_get(v_a_926_, 2);
lean_inc(v_offset_1004_);
v_y_1005_ = lean_ctor_get(v_a_926_, 3);
lean_inc(v_y_1005_);
v_ty_1006_ = lean_ctor_get(v_a_926_, 4);
lean_inc(v_ty_1006_);
v_b_1007_ = lean_ctor_get(v_a_926_, 5);
lean_inc(v_b_1007_);
lean_dec_ref_known(v_a_926_, 6);
v___x_1008_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__10));
v___x_1009_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1010_ = l_Nat_reprFast(v_x_1002_);
v___x_1011_ = lean_string_append(v___x_1009_, v___x_1010_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1008_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Nat_reprFast(v_i_1003_);
v___x_1017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1015_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17));
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Nat_reprFast(v_offset_1004_);
v___x_1022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1020_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__12));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1006_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = l_Nat_reprFast(v_y_1005_);
v___x_1031_ = lean_string_append(v___x_1009_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1029_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_box(1);
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_1007_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
return v___x_1039_;
}
case 21:
{
lean_object* v_x_1040_; lean_object* v_cidx_1041_; lean_object* v_b_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_x_1040_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_x_1040_);
v_cidx_1041_ = lean_ctor_get(v_a_926_, 1);
lean_inc(v_cidx_1041_);
v_b_1042_ = lean_ctor_get(v_a_926_, 2);
lean_inc(v_b_1042_);
lean_dec_ref_known(v_a_926_, 3);
v___x_1043_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__16));
v___x_1044_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1045_ = l_Nat_reprFast(v_x_1040_);
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1043_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l_Nat_reprFast(v_cidx_1041_);
v___x_1052_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1050_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_box(1);
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_1042_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
return v___x_1059_;
}
case 24:
{
lean_object* v_x_1060_; lean_object* v_n_1061_; lean_object* v_b_1062_; lean_object* v___x_1063_; lean_object* v___y_1065_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v_x_1060_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_x_1060_);
v_n_1061_ = lean_ctor_get(v_a_926_, 1);
lean_inc(v_n_1061_);
v_b_1062_ = lean_ctor_get(v_a_926_, 2);
lean_inc(v_b_1062_);
lean_dec_ref_known(v_a_926_, 3);
v___x_1063_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__18));
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_dec_eq(v_n_1061_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1082_ = l_Nat_reprFast(v_n_1061_);
v___x_1083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__20, &l_Lean_IR_formatFnBodyHead___closed__20_once, _init_l_Lean_IR_formatFnBodyHead___closed__20);
v___x_1085_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_1083_);
v___x_1087_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_1088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1084_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = 0;
v___x_1091_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*1, v___x_1090_);
v___y_1065_ = v___x_1091_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1092_; 
lean_dec(v_n_1061_);
v___x_1092_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__21));
v___y_1065_ = v___x_1092_;
goto v___jp_1064_;
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1063_);
lean_ctor_set(v___x_1066_, 1, v___y_1065_);
v___x_1067_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1070_ = l_Nat_reprFast(v_x_1060_);
v___x_1071_ = lean_string_append(v___x_1069_, v___x_1070_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1068_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_box(1);
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_1062_);
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
return v___x_1079_;
}
}
case 25:
{
lean_object* v_x_1093_; lean_object* v_n_1094_; lean_object* v_b_1095_; lean_object* v___x_1096_; lean_object* v___y_1098_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_x_1093_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_x_1093_);
v_n_1094_ = lean_ctor_get(v_a_926_, 1);
lean_inc(v_n_1094_);
v_b_1095_ = lean_ctor_get(v_a_926_, 2);
lean_inc(v_b_1095_);
lean_dec_ref_known(v_a_926_, 3);
v___x_1096_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__23));
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_dec_eq(v_n_1094_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1115_ = l_Nat_reprFast(v_n_1094_);
v___x_1116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
v___x_1117_ = lean_obj_once(&l_Lean_IR_formatFnBodyHead___closed__20, &l_Lean_IR_formatFnBodyHead___closed__20_once, _init_l_Lean_IR_formatFnBodyHead___closed__20);
v___x_1118_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1));
v___x_1119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v___x_1116_);
v___x_1120_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3));
v___x_1121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1117_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = 0;
v___x_1124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*1, v___x_1123_);
v___y_1098_ = v___x_1124_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1125_; 
lean_dec(v_n_1094_);
v___x_1125_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__21));
v___y_1098_ = v___x_1125_;
goto v___jp_1097_;
}
v___jp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1096_);
lean_ctor_set(v___x_1099_, 1, v___y_1098_);
v___x_1100_ = ((lean_object*)(l_Lean_IR_formatArray___redArg___lam__0___closed__1));
v___x_1101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1103_ = l_Nat_reprFast(v_x_1093_);
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1101_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_box(1);
v___x_1110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_1095_);
v___x_1112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
return v___x_1112_;
}
}
case 26:
{
lean_object* v_x_1126_; lean_object* v_b_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1145_; 
v_x_1126_ = lean_ctor_get(v_a_926_, 0);
v_b_1127_ = lean_ctor_get(v_a_926_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1129_ = v_a_926_;
v_isShared_1130_ = v_isSharedCheck_1145_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_b_1127_);
lean_inc(v_x_1126_);
lean_dec(v_a_926_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1145_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1131_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__25));
v___x_1132_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1133_ = l_Nat_reprFast(v_x_1126_);
v___x_1134_ = lean_string_append(v___x_1132_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 5);
lean_ctor_set(v___x_1129_, 1, v___x_1135_);
lean_ctor_set(v___x_1129_, 0, v___x_1131_);
v___x_1137_ = v___x_1129_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_box(1);
v___x_1141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_1127_);
v___x_1143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
return v___x_1143_;
}
}
}
case 27:
{
lean_object* v_x_1146_; lean_object* v_xType_1147_; lean_object* v_cs_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_x_1146_ = lean_ctor_get(v_a_926_, 1);
lean_inc(v_x_1146_);
v_xType_1147_ = lean_ctor_get(v_a_926_, 2);
lean_inc(v_xType_1147_);
v_cs_1148_ = lean_ctor_get(v_a_926_, 3);
lean_inc_ref(v_cs_1148_);
lean_dec_ref_known(v_a_926_, 4);
v___x_1149_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__27));
v___x_1150_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1151_ = l_Nat_reprFast(v_x_1146_);
v___x_1152_ = lean_string_append(v___x_1150_, v___x_1151_);
lean_dec_ref(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
v___x_1154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1149_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_xType_1147_);
v___x_1158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5));
v___x_1160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_array_get_size(v_cs_1148_);
v___x_1164_ = lean_nat_dec_lt(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
lean_dec_ref(v_cs_1148_);
lean_dec(v_indent_925_);
v___x_1165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1160_);
lean_ctor_set(v___x_1165_, 1, v___x_1161_);
return v___x_1165_;
}
else
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_nat_dec_le(v___x_1163_, v___x_1163_);
if (v___x_1166_ == 0)
{
if (v___x_1164_ == 0)
{
lean_object* v___x_1167_; 
lean_dec_ref(v_cs_1148_);
lean_dec(v_indent_925_);
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1160_);
lean_ctor_set(v___x_1167_, 1, v___x_1161_);
return v___x_1167_;
}
else
{
size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1168_ = ((size_t)0ULL);
v___x_1169_ = lean_usize_of_nat(v___x_1163_);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_925_, v_cs_1148_, v___x_1168_, v___x_1169_, v___x_1161_);
lean_dec_ref(v_cs_1148_);
v___x_1171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1160_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
return v___x_1171_;
}
}
else
{
size_t v___x_1172_; size_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1172_ = ((size_t)0ULL);
v___x_1173_ = lean_usize_of_nat(v___x_1163_);
v___x_1174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_925_, v_cs_1148_, v___x_1172_, v___x_1173_, v___x_1161_);
lean_dec_ref(v_cs_1148_);
v___x_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1160_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
return v___x_1175_;
}
}
}
case 29:
{
lean_object* v_j_1176_; lean_object* v_ys_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_indent_925_);
v_j_1176_ = lean_ctor_get(v_a_926_, 0);
v_ys_1177_ = lean_ctor_get(v_a_926_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1179_ = v_a_926_;
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_ys_1177_);
lean_inc(v_j_1176_);
lean_dec(v_a_926_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1181_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__31));
v___x_1182_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__0));
v___x_1183_ = l_Nat_reprFast(v_j_1176_);
v___x_1184_ = lean_string_append(v___x_1182_, v___x_1183_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 5);
lean_ctor_set(v___x_1179_, 1, v___x_1185_);
lean_ctor_set(v___x_1179_, 0, v___x_1181_);
v___x_1187_ = v___x_1179_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1177_);
lean_dec_ref(v_ys_1177_);
v___x_1189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
return v___x_1189_;
}
}
}
case 28:
{
lean_object* v_x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v_indent_925_);
v_x_1192_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_x_1192_);
lean_dec_ref_known(v_a_926_, 1);
v___x_1193_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__33));
v___x_1194_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_1192_);
v___x_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
return v___x_1195_;
}
case 30:
{
lean_object* v___x_1196_; 
lean_dec(v_indent_925_);
v___x_1196_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__35));
return v___x_1196_;
}
default: 
{
lean_object* v_x_1197_; lean_object* v_ty_1198_; lean_object* v_b_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_x_1197_ = l_Lean_IR_FnBody_targetVar(v_a_926_);
v_ty_1198_ = l_Lean_IR_FnBody_targetType(v_a_926_);
v_b_1199_ = l_Lean_IR_FnBody_body(v_a_926_);
v___x_1200_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__40));
v___x_1201_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0));
v___x_1202_ = l_Nat_reprFast(v_x_1197_);
v___x_1203_ = lean_string_append(v___x_1201_, v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1200_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1198_);
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = ((lean_object*)(l_Lean_IR_formatFnBodyHead___closed__14));
v___x_1211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_a_926_);
v___x_1213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3));
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_box(1);
v___x_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_925_, v_b_1199_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(lean_object* v_indent_1220_, lean_object* v_as_1221_, size_t v_i_1222_, size_t v_stop_1223_, lean_object* v_b_1224_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_eq(v_i_1222_, v_stop_1223_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; 
v___x_1226_ = lean_array_uget_borrowed(v_as_1221_, v_i_1222_);
v___x_1227_ = lean_box(1);
v___x_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_b_1224_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
lean_inc_n(v_indent_1220_, 2);
v___x_1229_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop), 2, 1);
lean_closure_set(v___x_1229_, 0, v_indent_1220_);
lean_inc(v___x_1226_);
v___x_1230_ = l_Lean_IR_formatAlt(v___x_1229_, v_indent_1220_, v___x_1226_);
v___x_1231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1228_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_i_1222_, v___x_1232_);
v_i_1222_ = v___x_1233_;
v_b_1224_ = v___x_1231_;
goto _start;
}
else
{
lean_dec(v_indent_1220_);
return v_b_1224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0___boxed(lean_object* v_indent_1235_, lean_object* v_as_1236_, lean_object* v_i_1237_, lean_object* v_stop_1238_, lean_object* v_b_1239_){
_start:
{
size_t v_i_boxed_1240_; size_t v_stop_boxed_1241_; lean_object* v_res_1242_; 
v_i_boxed_1240_ = lean_unbox_usize(v_i_1237_);
lean_dec(v_i_1237_);
v_stop_boxed_1241_ = lean_unbox_usize(v_stop_1238_);
lean_dec(v_stop_1238_);
v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_1235_, v_as_1236_, v_i_boxed_1240_, v_stop_boxed_1241_, v_b_1239_);
lean_dec_ref(v_as_1236_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody(lean_object* v_fnBody_1243_, lean_object* v_indent_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_1244_, v_fnBody_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatFnBody___lam__0(lean_object* v_fnBody_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_unsigned_to_nat(2u);
v___x_1248_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_1247_, v_fnBody_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringFnBody___lam__0(lean_object* v_b_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1252_ = lean_unsigned_to_nat(2u);
v___x_1253_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_1252_, v_b_1251_);
v___x_1254_ = l_Std_Format_defWidth;
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = l_Std_Format_pretty(v___x_1253_, v___x_1254_, v___x_1255_, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatDecl(lean_object* v_decl_1265_, lean_object* v_indent_1266_){
_start:
{
if (lean_obj_tag(v_decl_1265_) == 0)
{
lean_object* v_f_1267_; lean_object* v_xs_1268_; lean_object* v_type_1269_; lean_object* v_body_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_f_1267_ = lean_ctor_get(v_decl_1265_, 0);
lean_inc(v_f_1267_);
v_xs_1268_ = lean_ctor_get(v_decl_1265_, 1);
lean_inc_ref(v_xs_1268_);
v_type_1269_ = lean_ctor_get(v_decl_1265_, 2);
lean_inc(v_type_1269_);
v_body_1270_ = lean_ctor_get(v_decl_1265_, 3);
lean_inc(v_body_1270_);
lean_dec_ref_known(v_decl_1265_, 5);
v___x_1271_ = ((lean_object*)(l_Lean_IR_formatDecl___closed__1));
v___x_1272_ = 1;
v___x_1273_ = l_Lean_Name_toString(v_f_1267_, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1271_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_1268_);
lean_dec_ref(v_xs_1268_);
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_1269_);
v___x_1281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1));
v___x_1283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
lean_inc(v_indent_1266_);
v___x_1284_ = lean_nat_to_int(v_indent_1266_);
v___x_1285_ = lean_box(1);
v___x_1286_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v_indent_1266_, v_body_1270_);
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1284_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1283_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
return v___x_1289_;
}
else
{
lean_object* v_f_1290_; lean_object* v_xs_1291_; lean_object* v_type_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec(v_indent_1266_);
v_f_1290_ = lean_ctor_get(v_decl_1265_, 0);
lean_inc(v_f_1290_);
v_xs_1291_ = lean_ctor_get(v_decl_1265_, 1);
lean_inc_ref(v_xs_1291_);
v_type_1292_ = lean_ctor_get(v_decl_1265_, 2);
lean_inc(v_type_1292_);
lean_dec_ref_known(v_decl_1265_, 4);
v___x_1293_ = ((lean_object*)(l_Lean_IR_formatDecl___closed__3));
v___x_1294_ = 1;
v___x_1295_ = l_Lean_Name_toString(v_f_1290_, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1293_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_1291_);
lean_dec_ref(v_xs_1291_);
v___x_1299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = ((lean_object*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3));
v___x_1301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_1292_);
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatDecl___lam__0(lean_object* v_decl_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_unsigned_to_nat(2u);
v___x_1306_ = l_Lean_IR_formatDecl(v_decl_1304_, v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_declToString(lean_object* v_d_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1310_ = lean_unsigned_to_nat(2u);
v___x_1311_ = l_Lean_IR_formatDecl(v_d_1309_, v___x_1310_);
v___x_1312_ = l_Std_Format_defWidth;
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = l_Std_Format_pretty(v___x_1311_, v___x_1312_, v___x_1313_, v___x_1313_);
return v___x_1314_;
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
