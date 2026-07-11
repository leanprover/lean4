// Lean compiler output
// Module: Std.Internal.Parsec.Basic
// Imports: public import Init.NotationExtra public import Init.Data.ToString.Macro import Init.Data.Array.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_eof_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_eof_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_instReprError_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Internal.Parsec.Error.eof"};
static const lean_object* l_Std_Internal_Parsec_instReprError_repr___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instReprError_repr___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_instReprError_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instReprError_repr___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_instReprError_repr___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_instReprError_repr___closed__1_value;
static lean_once_cell_t l_Std_Internal_Parsec_instReprError_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_instReprError_repr___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_instReprError_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_instReprError_repr___closed__3;
static const lean_string_object l_Std_Internal_Parsec_instReprError_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Internal.Parsec.Error.other"};
static const lean_object* l_Std_Internal_Parsec_instReprError_repr___closed__4 = (const lean_object*)&l_Std_Internal_Parsec_instReprError_repr___closed__4_value;
static const lean_ctor_object l_Std_Internal_Parsec_instReprError_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instReprError_repr___closed__4_value)}};
static const lean_object* l_Std_Internal_Parsec_instReprError_repr___closed__5 = (const lean_object*)&l_Std_Internal_Parsec_instReprError_repr___closed__5_value;
static const lean_ctor_object l_Std_Internal_Parsec_instReprError_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instReprError_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Internal_Parsec_instReprError_repr___closed__6 = (const lean_object*)&l_Std_Internal_Parsec_instReprError_repr___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprError_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprError_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_instReprError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instReprError_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instReprError___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instReprError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Parsec_instReprError = (const lean_object*)&l_Std_Internal_Parsec_instReprError___closed__0_value;
static const lean_string_object l_Std_Internal_Parsec_instToStringError___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unexpected end of input"};
static const lean_object* l_Std_Internal_Parsec_instToStringError___lam__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instToStringError___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instToStringError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instToStringError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_instToStringError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instToStringError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instToStringError___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instToStringError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Parsec_instToStringError = (const lean_object*)&l_Std_Internal_Parsec_instToStringError___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_success_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_error_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Std.Internal.Parsec.ParseResult.success"};
static const lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2 = (const lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2_value;
static const lean_string_object l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Internal.Parsec.ParseResult.error"};
static const lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3 = (const lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value;
static const lean_ctor_object l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__3_value)}};
static const lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4 = (const lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5 = (const lean_object*)&l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Internal_Parsec_instInhabited___lam__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_instInhabited___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instInhabited___lam__0___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_instInhabited___lam__0___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_instInhabited___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___lam__0(lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_instInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instInhabited___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instInhabited___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instInhabited___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_instMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__0_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__1_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__2 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__2_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___lam__3, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__3 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__3_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___lam__4, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__4 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__4_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___lam__5, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__5 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__5_value;
static const lean_ctor_object l_Std_Internal_Parsec_instMonad___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__0_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__1_value)}};
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__6 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__6_value;
static const lean_ctor_object l_Std_Internal_Parsec_instMonad___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__6_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__2_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__3_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__4_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__5_value)}};
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__7 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__7_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_bind, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__8 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__8_value;
static const lean_ctor_object l_Std_Internal_Parsec_instMonad___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__7_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___closed__8_value)}};
static const lean_object* l_Std_Internal_Parsec_instMonad___closed__9 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___closed__9_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_instAlternative___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instAlternative___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instAlternative___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instAlternative___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_eof___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Internal_Parsec_eof___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_eof___redArg___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_eof___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_eof___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_eof___redArg___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_eof___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Internal_Parsec_many___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_Parsec_many___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_many___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_satisfy___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "condition not satisfied"};
static const lean_object* l_Std_Internal_Parsec_satisfy___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_satisfy___redArg___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_satisfy___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_satisfy___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_satisfy___redArg___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_satisfy___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_Internal_Parsec_Error_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_s_8_; lean_object* v___x_9_; 
v_s_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_s_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_s_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Internal_Parsec_Error_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_eof_elim___redArg(lean_object* v_t_22_, lean_object* v_eof_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_22_, v_eof_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_eof_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_eof_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_26_, v_eof_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_other_elim___redArg(lean_object* v_t_30_, lean_object* v_other_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_30_, v_other_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_other_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_other_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_34_, v_other_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instReprError_repr___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(2u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instReprError_repr___closed__3(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprError_repr(lean_object* v_x_51_, lean_object* v_prec_52_){
_start:
{
lean_object* v___y_54_; 
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1024u);
v___x_61_ = lean_nat_dec_le(v___x_60_, v_prec_52_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
v___y_54_ = v___x_62_;
goto v___jp_53_;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
v___y_54_ = v___x_63_;
goto v___jp_53_;
}
}
else
{
lean_object* v_s_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_84_; 
v_s_64_ = lean_ctor_get(v_x_51_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_84_ == 0)
{
v___x_66_ = v_x_51_;
v_isShared_67_ = v_isSharedCheck_84_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_s_64_);
lean_dec(v_x_51_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_84_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___y_69_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1024u);
v___x_81_ = lean_nat_dec_le(v___x_80_, v_prec_52_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
v___y_69_ = v___x_82_;
goto v___jp_68_;
}
else
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
v___y_69_ = v___x_83_;
goto v___jp_68_;
}
v___jp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_70_ = ((lean_object*)(l_Std_Internal_Parsec_instReprError_repr___closed__6));
v___x_71_ = l_String_quote(v_s_64_);
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 3);
lean_ctor_set(v___x_66_, 0, v___x_71_);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_79_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_70_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
lean_inc(v___y_69_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___y_69_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = 0;
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_76_);
v___x_78_ = l_Repr_addAppParen(v___x_77_, v_prec_52_);
return v___x_78_;
}
}
}
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_55_ = ((lean_object*)(l_Std_Internal_Parsec_instReprError_repr___closed__1));
lean_inc(v___y_54_);
v___x_56_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_56_, 0, v___y_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = 0;
v___x_58_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*1, v___x_57_);
v___x_59_ = l_Repr_addAppParen(v___x_58_, v_prec_52_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprError_repr___boxed(lean_object* v_x_85_, lean_object* v_prec_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Internal_Parsec_instReprError_repr(v_x_85_, v_prec_86_);
lean_dec(v_prec_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instToStringError___lam__0(lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_object* v___x_92_; 
v___x_92_ = ((lean_object*)(l_Std_Internal_Parsec_instToStringError___lam__0___closed__0));
return v___x_92_;
}
else
{
lean_object* v_s_93_; 
v_s_93_ = lean_ctor_get(v_x_91_, 0);
lean_inc_ref(v_s_93_);
return v_s_93_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instToStringError___lam__0___boxed(lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_Internal_Parsec_instToStringError___lam__0(v_x_94_);
lean_dec(v_x_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_unsigned_to_nat(0u);
return v___x_99_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_unsigned_to_nat(1u);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg___boxed(lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(v_x_101_);
lean_dec_ref(v_x_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b9_104_, lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___boxed(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b9_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Internal_Parsec_ParseResult_ctorIdx(v_00_u03b1_107_, v_00_u03b9_108_, v_x_109_);
lean_dec_ref(v_x_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(lean_object* v_t_111_, lean_object* v_k_112_){
_start:
{
lean_object* v_pos_113_; lean_object* v_res_114_; lean_object* v___x_115_; 
v_pos_113_ = lean_ctor_get(v_t_111_, 0);
lean_inc(v_pos_113_);
v_res_114_ = lean_ctor_get(v_t_111_, 1);
lean_inc(v_res_114_);
lean_dec_ref(v_t_111_);
v___x_115_ = lean_apply_2(v_k_112_, v_pos_113_, v_res_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim(lean_object* v_00_u03b1_116_, lean_object* v_00_u03b9_117_, lean_object* v_motive_118_, lean_object* v_ctorIdx_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_k_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_120_, v_k_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b9_125_, lean_object* v_motive_126_, lean_object* v_ctorIdx_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_k_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_Internal_Parsec_ParseResult_ctorElim(v_00_u03b1_124_, v_00_u03b9_125_, v_motive_126_, v_ctorIdx_127_, v_t_128_, v_h_129_, v_k_130_);
lean_dec(v_ctorIdx_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_success_elim___redArg(lean_object* v_t_132_, lean_object* v_success_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_132_, v_success_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_success_elim(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b9_136_, lean_object* v_motive_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_success_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_138_, v_success_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_error_elim___redArg(lean_object* v_t_142_, lean_object* v_error_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_142_, v_error_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_error_elim(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b9_146_, lean_object* v_motive_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_error_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_148_, v_error_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg(lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_x_166_, lean_object* v_prec_167_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v_pos_168_; lean_object* v_res_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_193_; 
v_pos_168_ = lean_ctor_get(v_x_166_, 0);
v_res_169_ = lean_ctor_get(v_x_166_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_193_ == 0)
{
v___x_171_ = v_x_166_;
v_isShared_172_ = v_isSharedCheck_193_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_res_169_);
lean_inc(v_pos_168_);
lean_dec(v_x_166_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_193_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___y_174_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(1024u);
v___x_190_ = lean_nat_dec_le(v___x_189_, v_prec_167_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
v___y_174_ = v___x_191_;
goto v___jp_173_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
v___y_174_ = v___x_192_;
goto v___jp_173_;
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_175_ = lean_box(1);
v___x_176_ = ((lean_object*)(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2));
v___x_177_ = lean_unsigned_to_nat(1024u);
v___x_178_ = lean_apply_2(v_inst_165_, v_pos_168_, v___x_177_);
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 5);
lean_ctor_set(v___x_171_, 1, v___x_178_);
lean_ctor_set(v___x_171_, 0, v___x_176_);
v___x_180_ = v___x_171_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_188_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_175_);
v___x_182_ = lean_apply_2(v_inst_164_, v_res_169_, v___x_177_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
lean_inc(v___y_174_);
v___x_184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_184_, 0, v___y_174_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = 0;
v___x_186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_185_);
v___x_187_ = l_Repr_addAppParen(v___x_186_, v_prec_167_);
return v___x_187_;
}
}
}
}
else
{
lean_object* v_pos_194_; lean_object* v_err_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_219_; 
lean_dec_ref(v_inst_164_);
v_pos_194_ = lean_ctor_get(v_x_166_, 0);
v_err_195_ = lean_ctor_get(v_x_166_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_219_ == 0)
{
v___x_197_ = v_x_166_;
v_isShared_198_ = v_isSharedCheck_219_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_err_195_);
lean_inc(v_pos_194_);
lean_dec(v_x_166_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_219_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___y_200_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(1024u);
v___x_216_ = lean_nat_dec_le(v___x_215_, v_prec_167_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
v___y_200_ = v___x_217_;
goto v___jp_199_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
v___y_200_ = v___x_218_;
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_201_ = lean_box(1);
v___x_202_ = ((lean_object*)(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5));
v___x_203_ = lean_unsigned_to_nat(1024u);
v___x_204_ = lean_apply_2(v_inst_165_, v_pos_194_, v___x_203_);
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 5);
lean_ctor_set(v___x_197_, 1, v___x_204_);
lean_ctor_set(v___x_197_, 0, v___x_202_);
v___x_206_ = v___x_197_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_214_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_201_);
v___x_208_ = l_Std_Internal_Parsec_instReprError_repr(v_err_195_, v___x_203_);
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
lean_inc(v___y_200_);
v___x_210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_210_, 0, v___y_200_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = 0;
v___x_212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*1, v___x_211_);
v___x_213_ = l_Repr_addAppParen(v___x_212_, v_prec_167_);
return v___x_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___boxed(lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_x_222_, lean_object* v_prec_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(v_inst_220_, v_inst_221_, v_x_222_, v_prec_223_);
lean_dec(v_prec_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b9_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_x_229_, lean_object* v_prec_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(v_inst_227_, v_inst_228_, v_x_229_, v_prec_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___boxed(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b9_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_x_236_, lean_object* v_prec_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_Internal_Parsec_instReprParseResult_repr(v_00_u03b1_232_, v_00_u03b9_233_, v_inst_234_, v_inst_235_, v_x_236_, v_prec_237_);
lean_dec(v_prec_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult___redArg(lean_object* v_inst_239_, lean_object* v_inst_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instReprParseResult_repr___boxed), 6, 4);
lean_closure_set(v___x_241_, 0, lean_box(0));
lean_closure_set(v___x_241_, 1, lean_box(0));
lean_closure_set(v___x_241_, 2, v_inst_239_);
lean_closure_set(v___x_241_, 3, v_inst_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b9_243_, lean_object* v_inst_244_, lean_object* v_inst_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instReprParseResult_repr___boxed), 6, 4);
lean_closure_set(v___x_246_, 0, lean_box(0));
lean_closure_set(v___x_246_, 1, lean_box(0));
lean_closure_set(v___x_246_, 2, v_inst_244_);
lean_closure_set(v___x_246_, 3, v_inst_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___lam__0(lean_object* v_it_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v_it_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited(lean_object* v_00_u03b1_254_, lean_object* v_00_u03b9_255_){
_start:
{
lean_object* v___f_256_; 
v___f_256_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___closed__0));
return v___f_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure___redArg(lean_object* v_a_257_, lean_object* v_it_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_it_258_);
lean_ctor_set(v___x_259_, 1, v_a_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure(lean_object* v_00_u03b1_260_, lean_object* v_00_u03b9_261_, lean_object* v_a_262_, lean_object* v_it_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_it_263_);
lean_ctor_set(v___x_264_, 1, v_a_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind___redArg(lean_object* v_f_265_, lean_object* v_g_266_, lean_object* v_it_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_apply_1(v_f_265_, v_it_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_pos_269_; lean_object* v_res_270_; lean_object* v___x_271_; 
v_pos_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_pos_269_);
v_res_270_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_res_270_);
lean_dec_ref_known(v___x_268_, 2);
v___x_271_ = lean_apply_2(v_g_266_, v_res_270_, v_pos_269_);
return v___x_271_;
}
else
{
lean_object* v_pos_272_; lean_object* v_err_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_g_266_);
v_pos_272_ = lean_ctor_get(v___x_268_, 0);
v_err_273_ = lean_ctor_get(v___x_268_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_268_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_err_273_);
lean_inc(v_pos_272_);
lean_dec(v___x_268_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_pos_272_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_err_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind(lean_object* v_00_u03b9_281_, lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_f_284_, lean_object* v_g_285_, lean_object* v_it_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_apply_1(v_f_284_, v_it_286_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_pos_288_; lean_object* v_res_289_; lean_object* v___x_290_; 
v_pos_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_pos_288_);
v_res_289_ = lean_ctor_get(v___x_287_, 1);
lean_inc(v_res_289_);
lean_dec_ref_known(v___x_287_, 2);
v___x_290_ = lean_apply_2(v_g_285_, v_res_289_, v_pos_288_);
return v___x_290_;
}
else
{
lean_object* v_pos_291_; lean_object* v_err_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_g_285_);
v_pos_291_ = lean_ctor_get(v___x_287_, 0);
v_err_292_ = lean_ctor_get(v___x_287_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_287_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_err_292_);
lean_inc(v_pos_291_);
lean_dec(v___x_287_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_pos_291_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_err_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail___redArg(lean_object* v_msg_300_, lean_object* v_it_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v_msg_300_);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v_it_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail(lean_object* v_00_u03b1_304_, lean_object* v_00_u03b9_305_, lean_object* v_msg_306_, lean_object* v_it_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v_msg_306_);
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v_it_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___redArg(lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_p_312_, lean_object* v_csuccess_313_, lean_object* v_cerror_314_, lean_object* v_it_315_){
_start:
{
lean_object* v___x_316_; 
lean_inc(v_it_315_);
v___x_316_ = lean_apply_1(v_p_312_, v_it_315_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_pos_317_; lean_object* v_res_318_; lean_object* v___x_319_; 
lean_dec(v_it_315_);
lean_dec_ref(v_cerror_314_);
lean_dec_ref(v_inst_311_);
lean_dec_ref(v_inst_310_);
v_pos_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_pos_317_);
v_res_318_ = lean_ctor_get(v___x_316_, 1);
lean_inc(v_res_318_);
lean_dec_ref_known(v___x_316_, 2);
v___x_319_ = lean_apply_2(v_csuccess_313_, v_res_318_, v_pos_317_);
return v___x_319_;
}
else
{
lean_object* v_pos_320_; lean_object* v_err_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_csuccess_313_);
v_pos_320_ = lean_ctor_get(v___x_316_, 0);
v_err_321_ = lean_ctor_get(v___x_316_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_335_ == 0)
{
v___x_323_ = v___x_316_;
v_isShared_324_ = v_isSharedCheck_335_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_err_321_);
lean_inc(v_pos_320_);
lean_dec(v___x_316_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_335_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_pos_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_pos_325_ = lean_ctor_get(v_inst_311_, 0);
lean_inc_n(v_pos_325_, 2);
lean_dec_ref(v_inst_311_);
v___x_326_ = lean_apply_1(v_pos_325_, v_it_315_);
lean_inc(v_pos_320_);
v___x_327_ = lean_apply_1(v_pos_325_, v_pos_320_);
v___x_328_ = lean_apply_2(v_inst_310_, v___x_326_, v___x_327_);
v___x_329_ = lean_unbox(v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v_cerror_314_);
if (v_isShared_324_ == 0)
{
v___x_331_ = v___x_323_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_pos_320_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_err_321_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_del_object(v___x_323_);
lean_dec(v_err_321_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_2(v_cerror_314_, v___x_333_, v_pos_320_);
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch(lean_object* v_00_u03b1_336_, lean_object* v_00_u03b9_337_, lean_object* v_elem_338_, lean_object* v_idx_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_00_u03b2_343_, lean_object* v_p_344_, lean_object* v_csuccess_345_, lean_object* v_cerror_346_, lean_object* v_it_347_){
_start:
{
lean_object* v___x_348_; 
lean_inc(v_it_347_);
v___x_348_ = lean_apply_1(v_p_344_, v_it_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_pos_349_; lean_object* v_res_350_; lean_object* v___x_351_; 
lean_dec(v_it_347_);
lean_dec_ref(v_cerror_346_);
lean_dec_ref(v_inst_342_);
lean_dec_ref(v_inst_340_);
v_pos_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_pos_349_);
v_res_350_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_res_350_);
lean_dec_ref_known(v___x_348_, 2);
v___x_351_ = lean_apply_2(v_csuccess_345_, v_res_350_, v_pos_349_);
return v___x_351_;
}
else
{
lean_object* v_pos_352_; lean_object* v_err_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v_csuccess_345_);
v_pos_352_ = lean_ctor_get(v___x_348_, 0);
v_err_353_ = lean_ctor_get(v___x_348_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_367_ == 0)
{
v___x_355_ = v___x_348_;
v_isShared_356_ = v_isSharedCheck_367_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_err_353_);
lean_inc(v_pos_352_);
lean_dec(v___x_348_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_367_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_pos_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_pos_357_ = lean_ctor_get(v_inst_342_, 0);
lean_inc_n(v_pos_357_, 2);
lean_dec_ref(v_inst_342_);
v___x_358_ = lean_apply_1(v_pos_357_, v_it_347_);
lean_inc(v_pos_352_);
v___x_359_ = lean_apply_1(v_pos_357_, v_pos_352_);
v___x_360_ = lean_apply_2(v_inst_340_, v___x_358_, v___x_359_);
v___x_361_ = lean_unbox(v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_363_; 
lean_dec_ref(v_cerror_346_);
if (v_isShared_356_ == 0)
{
v___x_363_ = v___x_355_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_pos_352_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_err_353_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_del_object(v___x_355_);
lean_dec(v_err_353_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_apply_2(v_cerror_346_, v___x_365_, v_pos_352_);
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___boxed(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b9_369_, lean_object* v_elem_370_, lean_object* v_idx_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_00_u03b2_375_, lean_object* v_p_376_, lean_object* v_csuccess_377_, lean_object* v_cerror_378_, lean_object* v_it_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Internal_Parsec_tryCatch(v_00_u03b1_368_, v_00_u03b9_369_, v_elem_370_, v_idx_371_, v_inst_372_, v_inst_373_, v_inst_374_, v_00_u03b2_375_, v_p_376_, v_csuccess_377_, v_cerror_378_, v_it_379_);
lean_dec_ref(v_inst_373_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__0(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_f_383_, lean_object* v_x_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_apply_1(v_x_384_, v___y_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_pos_387_; lean_object* v_res_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_pos_387_ = lean_ctor_get(v___x_386_, 0);
v_res_388_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v___x_386_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_res_388_);
lean_inc(v_pos_387_);
lean_dec(v___x_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_apply_1(v_f_383_, v_res_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_pos_387_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_pos_397_; lean_object* v_err_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_f_383_);
v_pos_397_ = lean_ctor_get(v___x_386_, 0);
v_err_398_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_386_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_err_398_);
lean_inc(v_pos_397_);
lean_dec(v___x_386_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_pos_397_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_err_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__1(lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_apply_1(v___y_409_, v___y_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_pos_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_pos_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_411_, 1);
lean_dec(v_unused_420_);
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_pos_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___y_408_);
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_pos_412_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___y_408_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_object* v_pos_421_; lean_object* v_err_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v___y_408_);
v_pos_421_ = lean_ctor_get(v___x_411_, 0);
v_err_422_ = lean_ctor_get(v___x_411_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_411_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_err_422_);
lean_inc(v_pos_421_);
lean_dec(v___x_411_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_pos_421_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_err_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__2(lean_object* v_00_u03b1_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___y_432_);
lean_ctor_set(v___x_433_, 1, v___y_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__3(lean_object* v_00_u03b1_434_, lean_object* v_00_u03b2_435_, lean_object* v_f_436_, lean_object* v_x_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_apply_1(v_f_436_, v___y_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_pos_440_; lean_object* v_res_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_pos_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_pos_440_);
v_res_441_ = lean_ctor_get(v___x_439_, 1);
lean_inc(v_res_441_);
lean_dec_ref_known(v___x_439_, 2);
v___x_442_ = lean_box(0);
v___x_443_ = lean_apply_2(v_x_437_, v___x_442_, v_pos_440_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_pos_444_; lean_object* v_res_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v_pos_444_ = lean_ctor_get(v___x_443_, 0);
v_res_445_ = lean_ctor_get(v___x_443_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v___x_443_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_res_445_);
lean_inc(v_pos_444_);
lean_dec(v___x_443_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_apply_1(v_res_441_, v_res_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_pos_444_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_object* v_pos_454_; lean_object* v_err_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec(v_res_441_);
v_pos_454_ = lean_ctor_get(v___x_443_, 0);
v_err_455_ = lean_ctor_get(v___x_443_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_443_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_err_455_);
lean_inc(v_pos_454_);
lean_dec(v___x_443_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_pos_454_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_err_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v_pos_463_; lean_object* v_err_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_x_437_);
v_pos_463_ = lean_ctor_get(v___x_439_, 0);
v_err_464_ = lean_ctor_get(v___x_439_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_439_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_err_464_);
lean_inc(v_pos_463_);
lean_dec(v___x_439_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_pos_463_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_err_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__4(lean_object* v_00_u03b1_472_, lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_apply_1(v_x_474_, v___y_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_pos_478_; lean_object* v_res_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_pos_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_pos_478_);
v_res_479_ = lean_ctor_get(v___x_477_, 1);
lean_inc(v_res_479_);
lean_dec_ref_known(v___x_477_, 2);
v___x_480_ = lean_box(0);
v___x_481_ = lean_apply_2(v_y_475_, v___x_480_, v_pos_478_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_pos_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_pos_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v___x_481_, 1);
lean_dec(v_unused_490_);
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_pos_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v_res_479_);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_pos_482_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_res_479_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_pos_491_; lean_object* v_err_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_res_479_);
v_pos_491_ = lean_ctor_get(v___x_481_, 0);
v_err_492_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_481_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_err_492_);
lean_inc(v_pos_491_);
lean_dec(v___x_481_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_pos_491_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_err_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_dec_ref(v_y_475_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__5(lean_object* v_00_u03b1_500_, lean_object* v_00_u03b2_501_, lean_object* v_x_502_, lean_object* v_y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = lean_apply_1(v_x_502_, v___y_504_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_pos_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_pos_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_pos_506_);
lean_dec_ref_known(v___x_505_, 2);
v___x_507_ = lean_box(0);
v___x_508_ = lean_apply_2(v_y_503_, v___x_507_, v_pos_506_);
return v___x_508_;
}
else
{
lean_object* v_pos_509_; lean_object* v_err_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_y_503_);
v_pos_509_ = lean_ctor_get(v___x_505_, 0);
v_err_510_ = lean_ctor_get(v___x_505_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_505_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_err_510_);
lean_inc(v_pos_509_);
lean_dec(v___x_505_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_pos_509_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_err_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad(lean_object* v_00_u03b9_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___closed__9));
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___redArg(lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_p_541_, lean_object* v_q_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_544_; 
lean_inc(v_a_543_);
v___x_544_ = lean_apply_1(v_p_541_, v_a_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_dec(v_a_543_);
lean_dec_ref(v_q_542_);
lean_dec_ref(v_inst_540_);
lean_dec_ref(v_inst_539_);
return v___x_544_;
}
else
{
lean_object* v_pos_545_; lean_object* v_pos_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_pos_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_n(v_pos_545_, 2);
v_pos_546_ = lean_ctor_get(v_inst_540_, 0);
lean_inc_n(v_pos_546_, 2);
lean_dec_ref(v_inst_540_);
v___x_547_ = lean_apply_1(v_pos_546_, v_a_543_);
v___x_548_ = lean_apply_1(v_pos_546_, v_pos_545_);
v___x_549_ = lean_apply_2(v_inst_539_, v___x_547_, v___x_548_);
v___x_550_ = lean_unbox(v___x_549_);
if (v___x_550_ == 0)
{
lean_dec(v_pos_545_);
lean_dec_ref(v_q_542_);
return v___x_544_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec_ref_known(v___x_544_, 2);
v___x_551_ = lean_box(0);
v___x_552_ = lean_apply_2(v_q_542_, v___x_551_, v_pos_545_);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b9_554_, lean_object* v_elem_555_, lean_object* v_idx_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_p_560_, lean_object* v_q_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_563_; 
lean_inc(v_a_562_);
v___x_563_ = lean_apply_1(v_p_560_, v_a_562_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_dec(v_a_562_);
lean_dec_ref(v_q_561_);
lean_dec_ref(v_inst_559_);
lean_dec_ref(v_inst_557_);
return v___x_563_;
}
else
{
lean_object* v_pos_564_; lean_object* v_pos_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_pos_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_n(v_pos_564_, 2);
v_pos_565_ = lean_ctor_get(v_inst_559_, 0);
lean_inc_n(v_pos_565_, 2);
lean_dec_ref(v_inst_559_);
v___x_566_ = lean_apply_1(v_pos_565_, v_a_562_);
v___x_567_ = lean_apply_1(v_pos_565_, v_pos_564_);
v___x_568_ = lean_apply_2(v_inst_557_, v___x_566_, v___x_567_);
v___x_569_ = lean_unbox(v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v_pos_564_);
lean_dec_ref(v_q_561_);
return v___x_563_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref_known(v___x_563_, 2);
v___x_570_ = lean_box(0);
v___x_571_ = lean_apply_2(v_q_561_, v___x_570_, v_pos_564_);
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___boxed(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b9_573_, lean_object* v_elem_574_, lean_object* v_idx_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_p_579_, lean_object* v_q_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Internal_Parsec_orElse(v_00_u03b1_572_, v_00_u03b9_573_, v_elem_574_, v_idx_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_p_579_, v_q_580_, v_a_581_);
lean_dec_ref(v_inst_577_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt___redArg(lean_object* v_p_583_, lean_object* v_it_584_){
_start:
{
lean_object* v___x_585_; 
lean_inc(v_it_584_);
v___x_585_ = lean_apply_1(v_p_583_, v_it_584_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_dec(v_it_584_);
return v___x_585_;
}
else
{
lean_object* v_err_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_err_586_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_585_, 0);
lean_dec(v_unused_594_);
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_err_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_it_584_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_it_584_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_err_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt(lean_object* v_00_u03b1_595_, lean_object* v_00_u03b9_596_, lean_object* v_p_597_, lean_object* v_it_598_){
_start:
{
lean_object* v___x_599_; 
lean_inc(v_it_598_);
v___x_599_ = lean_apply_1(v_p_597_, v_it_598_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_dec(v_it_598_);
return v___x_599_;
}
else
{
lean_object* v_err_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_err_600_ = lean_ctor_get(v___x_599_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v___x_599_, 0);
lean_dec(v_unused_608_);
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_err_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_it_598_);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_it_598_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_err_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__0(lean_object* v_00_u03b1_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v___y_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__1(lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_00_u03b1_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_619_; 
lean_inc(v___y_618_);
v___x_619_ = lean_apply_1(v___y_616_, v___y_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec_ref(v_inst_614_);
lean_dec_ref(v_inst_613_);
return v___x_619_;
}
else
{
lean_object* v_pos_620_; lean_object* v_pos_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_pos_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_n(v_pos_620_, 2);
v_pos_621_ = lean_ctor_get(v_inst_613_, 0);
lean_inc_n(v_pos_621_, 2);
lean_dec_ref(v_inst_613_);
v___x_622_ = lean_apply_1(v_pos_621_, v___y_618_);
v___x_623_ = lean_apply_1(v_pos_621_, v_pos_620_);
v___x_624_ = lean_apply_2(v_inst_614_, v___x_622_, v___x_623_);
v___x_625_ = lean_unbox(v___x_624_);
if (v___x_625_ == 0)
{
lean_dec(v_pos_620_);
lean_dec_ref(v___y_617_);
return v___x_619_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref_known(v___x_619_, 2);
v___x_626_ = lean_box(0);
v___x_627_ = lean_apply_2(v___y_617_, v___x_626_, v_pos_620_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg(lean_object* v_inst_629_, lean_object* v_inst_630_){
_start:
{
lean_object* v___f_631_; lean_object* v___f_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___f_631_ = ((lean_object*)(l_Std_Internal_Parsec_instAlternative___redArg___closed__0));
v___f_632_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___redArg___lam__1), 6, 2);
lean_closure_set(v___f_632_, 0, v_inst_630_);
lean_closure_set(v___f_632_, 1, v_inst_629_);
v___x_633_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___closed__7));
v___x_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___f_631_);
lean_ctor_set(v___x_634_, 2, v___f_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative(lean_object* v_00_u03b9_635_, lean_object* v_elem_636_, lean_object* v_idx_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_inst_640_){
_start:
{
lean_object* v___f_641_; lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___f_641_ = ((lean_object*)(l_Std_Internal_Parsec_instAlternative___redArg___closed__0));
v___f_642_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___redArg___lam__1), 6, 2);
lean_closure_set(v___f_642_, 0, v_inst_640_);
lean_closure_set(v___f_642_, 1, v_inst_638_);
v___x_643_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___closed__7));
v___x_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___f_641_);
lean_ctor_set(v___x_644_, 2, v___f_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___boxed(lean_object* v_00_u03b9_645_, lean_object* v_elem_646_, lean_object* v_idx_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Internal_Parsec_instAlternative(v_00_u03b9_645_, v_elem_646_, v_idx_647_, v_inst_648_, v_inst_649_, v_inst_650_);
lean_dec_ref(v_inst_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___redArg(lean_object* v_inst_655_, lean_object* v_it_656_){
_start:
{
lean_object* v_hasNext_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_hasNext_657_ = lean_ctor_get(v_inst_655_, 3);
lean_inc_ref(v_hasNext_657_);
lean_dec_ref(v_inst_655_);
lean_inc(v_it_656_);
v___x_658_ = lean_apply_1(v_hasNext_657_, v_it_656_);
v___x_659_ = lean_unbox(v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_it_656_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Std_Internal_Parsec_eof___redArg___closed__1));
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v_it_656_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof(lean_object* v_00_u03b9_664_, lean_object* v_elem_665_, lean_object* v_idx_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_it_670_){
_start:
{
lean_object* v_hasNext_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_hasNext_671_ = lean_ctor_get(v_inst_669_, 3);
lean_inc_ref(v_hasNext_671_);
lean_dec_ref(v_inst_669_);
lean_inc(v_it_670_);
v___x_672_ = lean_apply_1(v_hasNext_671_, v_it_670_);
v___x_673_ = lean_unbox(v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_it_670_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Std_Internal_Parsec_eof___redArg___closed__1));
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v_it_670_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___boxed(lean_object* v_00_u03b9_678_, lean_object* v_elem_679_, lean_object* v_idx_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_it_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_Internal_Parsec_eof(v_00_u03b9_678_, v_elem_679_, v_idx_680_, v_inst_681_, v_inst_682_, v_inst_683_, v_it_684_);
lean_dec_ref(v_inst_682_);
lean_dec_ref(v_inst_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___redArg(lean_object* v_inst_686_, lean_object* v_it_687_){
_start:
{
lean_object* v_hasNext_688_; lean_object* v___x_689_; uint8_t v___x_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_hasNext_688_ = lean_ctor_get(v_inst_686_, 3);
lean_inc_ref(v_hasNext_688_);
lean_dec_ref(v_inst_686_);
lean_inc(v_it_687_);
v___x_689_ = lean_apply_1(v_hasNext_688_, v_it_687_);
v___x_690_ = lean_unbox(v___x_689_);
v___x_691_ = lean_bool_not(v___x_690_);
v___x_692_ = lean_box(v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_it_687_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof(lean_object* v_00_u03b9_694_, lean_object* v_elem_695_, lean_object* v_idx_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_it_700_){
_start:
{
lean_object* v_hasNext_701_; lean_object* v___x_702_; uint8_t v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_hasNext_701_ = lean_ctor_get(v_inst_699_, 3);
lean_inc_ref(v_hasNext_701_);
lean_dec_ref(v_inst_699_);
lean_inc(v_it_700_);
v___x_702_ = lean_apply_1(v_hasNext_701_, v_it_700_);
v___x_703_ = lean_unbox(v___x_702_);
v___x_704_ = lean_bool_not(v___x_703_);
v___x_705_ = lean_box(v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_it_700_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___boxed(lean_object* v_00_u03b9_707_, lean_object* v_elem_708_, lean_object* v_idx_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_it_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_Internal_Parsec_isEof(v_00_u03b9_707_, v_elem_708_, v_idx_709_, v_inst_710_, v_inst_711_, v_inst_712_, v_it_713_);
lean_dec_ref(v_inst_711_);
lean_dec_ref(v_inst_710_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___redArg(lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_p_717_, lean_object* v_acc_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___x_720_; 
lean_inc_ref(v_p_717_);
lean_inc(v_a_719_);
v___x_720_ = lean_apply_1(v_p_717_, v_a_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_pos_721_; lean_object* v_res_722_; lean_object* v___x_723_; 
lean_dec(v_a_719_);
v_pos_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_pos_721_);
v_res_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_res_722_);
lean_dec_ref_known(v___x_720_, 2);
v___x_723_ = lean_array_push(v_acc_718_, v_res_722_);
v_acc_718_ = v___x_723_;
v_a_719_ = v_pos_721_;
goto _start;
}
else
{
lean_object* v_pos_725_; lean_object* v_err_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref(v_p_717_);
v_pos_725_ = lean_ctor_get(v___x_720_, 0);
v_err_726_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_741_ == 0)
{
v___x_728_ = v___x_720_;
v_isShared_729_ = v_isSharedCheck_741_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_err_726_);
lean_inc(v_pos_725_);
lean_dec(v___x_720_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_741_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_pos_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_pos_730_ = lean_ctor_get(v_inst_716_, 0);
lean_inc_n(v_pos_730_, 2);
lean_dec_ref(v_inst_716_);
v___x_731_ = lean_apply_1(v_pos_730_, v_a_719_);
lean_inc(v_pos_725_);
v___x_732_ = lean_apply_1(v_pos_730_, v_pos_725_);
v___x_733_ = lean_apply_2(v_inst_715_, v___x_731_, v___x_732_);
v___x_734_ = lean_unbox(v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_736_; 
lean_dec_ref(v_acc_718_);
if (v_isShared_729_ == 0)
{
v___x_736_ = v___x_728_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_pos_725_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_err_726_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
lean_object* v___x_739_; 
lean_dec(v_err_726_);
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 0);
lean_ctor_set(v___x_728_, 1, v_acc_718_);
v___x_739_ = v___x_728_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_pos_725_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_acc_718_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b9_743_, lean_object* v_elem_744_, lean_object* v_idx_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_p_749_, lean_object* v_acc_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_746_, v_inst_748_, v_p_749_, v_acc_750_, v_a_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___boxed(lean_object* v_00_u03b1_753_, lean_object* v_00_u03b9_754_, lean_object* v_elem_755_, lean_object* v_idx_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_p_760_, lean_object* v_acc_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_Internal_Parsec_manyCore(v_00_u03b1_753_, v_00_u03b9_754_, v_elem_755_, v_idx_756_, v_inst_757_, v_inst_758_, v_inst_759_, v_p_760_, v_acc_761_, v_a_762_);
lean_dec_ref(v_inst_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___redArg(lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_p_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Std_Internal_Parsec_many___redArg___closed__0));
v___x_771_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_766_, v_inst_767_, v_p_768_, v___x_770_, v_a_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b9_773_, lean_object* v_elem_774_, lean_object* v_idx_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_p_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Std_Internal_Parsec_many___redArg___closed__0));
v___x_782_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_776_, v_inst_778_, v_p_779_, v___x_781_, v_a_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___boxed(lean_object* v_00_u03b1_783_, lean_object* v_00_u03b9_784_, lean_object* v_elem_785_, lean_object* v_idx_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_p_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_Internal_Parsec_many(v_00_u03b1_783_, v_00_u03b9_784_, v_elem_785_, v_idx_786_, v_inst_787_, v_inst_788_, v_inst_789_, v_p_790_, v_a_791_);
lean_dec_ref(v_inst_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___redArg(lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_p_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_797_; 
lean_inc_ref(v_p_795_);
v___x_797_ = lean_apply_1(v_p_795_, v_a_796_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_pos_798_; lean_object* v_res_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_pos_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_pos_798_);
v_res_799_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_res_799_);
lean_dec_ref_known(v___x_797_, 2);
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = lean_mk_empty_array_with_capacity(v___x_800_);
v___x_802_ = lean_array_push(v___x_801_, v_res_799_);
v___x_803_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_793_, v_inst_794_, v_p_795_, v___x_802_, v_pos_798_);
return v___x_803_;
}
else
{
lean_object* v_pos_804_; lean_object* v_err_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v_p_795_);
lean_dec_ref(v_inst_794_);
lean_dec_ref(v_inst_793_);
v_pos_804_ = lean_ctor_get(v___x_797_, 0);
v_err_805_ = lean_ctor_get(v___x_797_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_797_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_err_805_);
lean_inc(v_pos_804_);
lean_dec(v___x_797_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_pos_804_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_err_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1(lean_object* v_00_u03b1_813_, lean_object* v_00_u03b9_814_, lean_object* v_elem_815_, lean_object* v_idx_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_p_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_822_; 
lean_inc_ref(v_p_820_);
v___x_822_ = lean_apply_1(v_p_820_, v_a_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_pos_823_; lean_object* v_res_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_pos_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_pos_823_);
v_res_824_ = lean_ctor_get(v___x_822_, 1);
lean_inc(v_res_824_);
lean_dec_ref_known(v___x_822_, 2);
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_mk_empty_array_with_capacity(v___x_825_);
v___x_827_ = lean_array_push(v___x_826_, v_res_824_);
v___x_828_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_817_, v_inst_819_, v_p_820_, v___x_827_, v_pos_823_);
return v___x_828_;
}
else
{
lean_object* v_pos_829_; lean_object* v_err_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_p_820_);
lean_dec_ref(v_inst_819_);
lean_dec_ref(v_inst_817_);
v_pos_829_ = lean_ctor_get(v___x_822_, 0);
v_err_830_ = lean_ctor_get(v___x_822_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_822_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_err_830_);
lean_inc(v_pos_829_);
lean_dec(v___x_822_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_pos_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_err_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___boxed(lean_object* v_00_u03b1_838_, lean_object* v_00_u03b9_839_, lean_object* v_elem_840_, lean_object* v_idx_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_p_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_Internal_Parsec_many1(v_00_u03b1_838_, v_00_u03b9_839_, v_elem_840_, v_idx_841_, v_inst_842_, v_inst_843_, v_inst_844_, v_p_845_, v_a_846_);
lean_dec_ref(v_inst_843_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___redArg(lean_object* v_inst_848_, lean_object* v_it_849_){
_start:
{
lean_object* v_hasNext_850_; lean_object* v_next_x27_851_; lean_object* v_curr_x27_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_hasNext_850_ = lean_ctor_get(v_inst_848_, 3);
lean_inc_ref(v_hasNext_850_);
v_next_x27_851_ = lean_ctor_get(v_inst_848_, 4);
lean_inc(v_next_x27_851_);
v_curr_x27_852_ = lean_ctor_get(v_inst_848_, 5);
lean_inc(v_curr_x27_852_);
lean_dec_ref(v_inst_848_);
lean_inc(v_it_849_);
v___x_853_ = lean_apply_1(v_hasNext_850_, v_it_849_);
v___x_854_ = lean_unbox(v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v_curr_x27_852_);
lean_dec(v_next_x27_851_);
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v_it_849_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
return v___x_856_;
}
else
{
lean_object* v_c_857_; lean_object* v_it_x27_858_; lean_object* v___x_859_; 
lean_inc(v_it_849_);
v_c_857_ = lean_apply_2(v_curr_x27_852_, v_it_849_, lean_box(0));
v_it_x27_858_ = lean_apply_2(v_next_x27_851_, v_it_849_, lean_box(0));
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_it_x27_858_);
lean_ctor_set(v___x_859_, 1, v_c_857_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any(lean_object* v_00_u03b9_860_, lean_object* v_elem_861_, lean_object* v_idx_862_, lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_it_866_){
_start:
{
lean_object* v_hasNext_867_; lean_object* v_next_x27_868_; lean_object* v_curr_x27_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_hasNext_867_ = lean_ctor_get(v_inst_865_, 3);
lean_inc_ref(v_hasNext_867_);
v_next_x27_868_ = lean_ctor_get(v_inst_865_, 4);
lean_inc(v_next_x27_868_);
v_curr_x27_869_ = lean_ctor_get(v_inst_865_, 5);
lean_inc(v_curr_x27_869_);
lean_dec_ref(v_inst_865_);
lean_inc(v_it_866_);
v___x_870_ = lean_apply_1(v_hasNext_867_, v_it_866_);
v___x_871_ = lean_unbox(v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v_curr_x27_869_);
lean_dec(v_next_x27_868_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v_it_866_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
return v___x_873_;
}
else
{
lean_object* v_c_874_; lean_object* v_it_x27_875_; lean_object* v___x_876_; 
lean_inc(v_it_866_);
v_c_874_ = lean_apply_2(v_curr_x27_869_, v_it_866_, lean_box(0));
v_it_x27_875_ = lean_apply_2(v_next_x27_868_, v_it_866_, lean_box(0));
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_it_x27_875_);
lean_ctor_set(v___x_876_, 1, v_c_874_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___boxed(lean_object* v_00_u03b9_877_, lean_object* v_elem_878_, lean_object* v_idx_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_it_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Internal_Parsec_any(v_00_u03b9_877_, v_elem_878_, v_idx_879_, v_inst_880_, v_inst_881_, v_inst_882_, v_it_883_);
lean_dec_ref(v_inst_881_);
lean_dec_ref(v_inst_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___redArg(lean_object* v_inst_888_, lean_object* v_p_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_hasNext_891_; lean_object* v_next_x27_892_; lean_object* v_curr_x27_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_hasNext_891_ = lean_ctor_get(v_inst_888_, 3);
lean_inc_ref(v_hasNext_891_);
v_next_x27_892_ = lean_ctor_get(v_inst_888_, 4);
lean_inc(v_next_x27_892_);
v_curr_x27_893_ = lean_ctor_get(v_inst_888_, 5);
lean_inc(v_curr_x27_893_);
lean_dec_ref(v_inst_888_);
lean_inc(v_a_890_);
v___x_894_ = lean_apply_1(v_hasNext_891_, v_a_890_);
v___x_895_ = lean_unbox(v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_curr_x27_893_);
lean_dec(v_next_x27_892_);
lean_dec_ref(v_p_889_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_897_, 0, v_a_890_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v_c_898_; lean_object* v_it_x27_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
lean_inc_n(v_a_890_, 2);
v_c_898_ = lean_apply_2(v_curr_x27_893_, v_a_890_, lean_box(0));
v_it_x27_899_ = lean_apply_2(v_next_x27_892_, v_a_890_, lean_box(0));
lean_inc(v_c_898_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_it_x27_899_);
lean_ctor_set(v___x_900_, 1, v_c_898_);
v___x_901_ = lean_apply_1(v_p_889_, v_c_898_);
v___x_902_ = lean_unbox(v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec_ref_known(v___x_900_, 2);
v___x_903_ = ((lean_object*)(l_Std_Internal_Parsec_satisfy___redArg___closed__1));
v___x_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_904_, 0, v_a_890_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
return v___x_904_;
}
else
{
lean_dec(v_a_890_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy(lean_object* v_00_u03b9_905_, lean_object* v_elem_906_, lean_object* v_idx_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_p_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_hasNext_913_; lean_object* v_next_x27_914_; lean_object* v_curr_x27_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_hasNext_913_ = lean_ctor_get(v_inst_910_, 3);
lean_inc_ref(v_hasNext_913_);
v_next_x27_914_ = lean_ctor_get(v_inst_910_, 4);
lean_inc(v_next_x27_914_);
v_curr_x27_915_ = lean_ctor_get(v_inst_910_, 5);
lean_inc(v_curr_x27_915_);
lean_dec_ref(v_inst_910_);
lean_inc(v_a_912_);
v___x_916_ = lean_apply_1(v_hasNext_913_, v_a_912_);
v___x_917_ = lean_unbox(v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_curr_x27_915_);
lean_dec(v_next_x27_914_);
lean_dec_ref(v_p_911_);
v___x_918_ = lean_box(0);
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v_a_912_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
return v___x_919_;
}
else
{
lean_object* v_c_920_; lean_object* v_it_x27_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
lean_inc_n(v_a_912_, 2);
v_c_920_ = lean_apply_2(v_curr_x27_915_, v_a_912_, lean_box(0));
v_it_x27_921_ = lean_apply_2(v_next_x27_914_, v_a_912_, lean_box(0));
lean_inc(v_c_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_it_x27_921_);
lean_ctor_set(v___x_922_, 1, v_c_920_);
v___x_923_ = lean_apply_1(v_p_911_, v_c_920_);
v___x_924_ = lean_unbox(v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref_known(v___x_922_, 2);
v___x_925_ = ((lean_object*)(l_Std_Internal_Parsec_satisfy___redArg___closed__1));
v___x_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_926_, 0, v_a_912_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
return v___x_926_;
}
else
{
lean_dec(v_a_912_);
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___boxed(lean_object* v_00_u03b9_927_, lean_object* v_elem_928_, lean_object* v_idx_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_p_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_Internal_Parsec_satisfy(v_00_u03b9_927_, v_elem_928_, v_idx_929_, v_inst_930_, v_inst_931_, v_inst_932_, v_p_933_, v_a_934_);
lean_dec_ref(v_inst_931_);
lean_dec_ref(v_inst_930_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy___redArg(lean_object* v_p_936_, lean_object* v_it_937_){
_start:
{
lean_object* v___x_938_; 
lean_inc(v_it_937_);
v___x_938_ = lean_apply_1(v_p_936_, v_it_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_946_; 
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; lean_object* v_unused_948_; 
v_unused_947_ = lean_ctor_get(v___x_938_, 1);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v___x_938_, 0);
lean_dec(v_unused_948_);
v___x_940_ = v___x_938_;
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
else
{
lean_dec(v___x_938_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
lean_ctor_set(v___x_940_, 1, v___x_942_);
lean_ctor_set(v___x_940_, 0, v_it_937_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_it_937_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; lean_object* v_unused_958_; 
v_unused_957_ = lean_ctor_get(v___x_938_, 1);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v___x_938_, 0);
lean_dec(v_unused_958_);
v___x_950_ = v___x_938_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_dec(v___x_938_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_box(0);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 0);
lean_ctor_set(v___x_950_, 1, v___x_952_);
lean_ctor_set(v___x_950_, 0, v_it_937_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_it_937_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b9_960_, lean_object* v_p_961_, lean_object* v_it_962_){
_start:
{
lean_object* v___x_963_; 
lean_inc(v_it_962_);
v___x_963_ = lean_apply_1(v_p_961_, v_it_962_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_971_; 
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_972_ = lean_ctor_get(v___x_963_, 1);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_973_);
v___x_965_ = v___x_963_;
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
else
{
lean_dec(v___x_963_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 1);
lean_ctor_set(v___x_965_, 1, v___x_967_);
lean_ctor_set(v___x_965_, 0, v_it_962_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_it_962_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; lean_object* v_unused_983_; 
v_unused_982_ = lean_ctor_get(v___x_963_, 1);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_983_);
v___x_975_ = v___x_963_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_dec(v___x_963_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = lean_box(0);
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 0);
lean_ctor_set(v___x_975_, 1, v___x_977_);
lean_ctor_set(v___x_975_, 0, v_it_962_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_it_962_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___redArg(lean_object* v_inst_984_, lean_object* v_it_985_){
_start:
{
lean_object* v_hasNext_986_; lean_object* v_curr_x27_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_hasNext_986_ = lean_ctor_get(v_inst_984_, 3);
lean_inc_ref(v_hasNext_986_);
v_curr_x27_987_ = lean_ctor_get(v_inst_984_, 5);
lean_inc(v_curr_x27_987_);
lean_dec_ref(v_inst_984_);
lean_inc(v_it_985_);
v___x_988_ = lean_apply_1(v_hasNext_986_, v_it_985_);
v___x_989_ = lean_unbox(v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v_curr_x27_987_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_it_985_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_inc(v_it_985_);
v___x_992_ = lean_apply_2(v_curr_x27_987_, v_it_985_, lean_box(0));
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v_it_985_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f(lean_object* v_00_u03b9_995_, lean_object* v_elem_996_, lean_object* v_idx_997_, lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_it_1001_){
_start:
{
lean_object* v_hasNext_1002_; lean_object* v_curr_x27_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_hasNext_1002_ = lean_ctor_get(v_inst_1000_, 3);
lean_inc_ref(v_hasNext_1002_);
v_curr_x27_1003_ = lean_ctor_get(v_inst_1000_, 5);
lean_inc(v_curr_x27_1003_);
lean_dec_ref(v_inst_1000_);
lean_inc(v_it_1001_);
v___x_1004_ = lean_apply_1(v_hasNext_1002_, v_it_1001_);
v___x_1005_ = lean_unbox(v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v_curr_x27_1003_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_it_1001_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_inc(v_it_1001_);
v___x_1008_ = lean_apply_2(v_curr_x27_1003_, v_it_1001_, lean_box(0));
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_it_1001_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___boxed(lean_object* v_00_u03b9_1011_, lean_object* v_elem_1012_, lean_object* v_idx_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_it_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_Internal_Parsec_peek_x3f(v_00_u03b9_1011_, v_elem_1012_, v_idx_1013_, v_inst_1014_, v_inst_1015_, v_inst_1016_, v_it_1017_);
lean_dec_ref(v_inst_1015_);
lean_dec_ref(v_inst_1014_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___redArg(lean_object* v_inst_1019_, lean_object* v_p_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_hasNext_1022_; lean_object* v_curr_x27_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_hasNext_1022_ = lean_ctor_get(v_inst_1019_, 3);
lean_inc_ref(v_hasNext_1022_);
v_curr_x27_1023_ = lean_ctor_get(v_inst_1019_, 5);
lean_inc(v_curr_x27_1023_);
lean_dec_ref(v_inst_1019_);
lean_inc(v_a_1021_);
v___x_1024_ = lean_apply_1(v_hasNext_1022_, v_a_1021_);
v___x_1025_ = lean_unbox(v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec(v_curr_x27_1023_);
lean_dec_ref(v_p_1020_);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_a_1021_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
lean_inc(v_a_1021_);
v___x_1028_ = lean_apply_2(v_curr_x27_1023_, v_a_1021_, lean_box(0));
lean_inc(v___x_1028_);
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
v___x_1030_ = lean_apply_1(v_p_1020_, v___x_1028_);
v___x_1031_ = lean_unbox(v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref_known(v___x_1029_, 1);
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_a_1021_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_a_1021_);
lean_ctor_set(v___x_1034_, 1, v___x_1029_);
return v___x_1034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f(lean_object* v_00_u03b9_1035_, lean_object* v_elem_1036_, lean_object* v_idx_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_p_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_hasNext_1043_; lean_object* v_curr_x27_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_hasNext_1043_ = lean_ctor_get(v_inst_1040_, 3);
lean_inc_ref(v_hasNext_1043_);
v_curr_x27_1044_ = lean_ctor_get(v_inst_1040_, 5);
lean_inc(v_curr_x27_1044_);
lean_dec_ref(v_inst_1040_);
lean_inc(v_a_1042_);
v___x_1045_ = lean_apply_1(v_hasNext_1043_, v_a_1042_);
v___x_1046_ = lean_unbox(v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_curr_x27_1044_);
lean_dec_ref(v_p_1041_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1042_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
lean_inc(v_a_1042_);
v___x_1049_ = lean_apply_2(v_curr_x27_1044_, v_a_1042_, lean_box(0));
lean_inc(v___x_1049_);
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
v___x_1051_ = lean_apply_1(v_p_1041_, v___x_1049_);
v___x_1052_ = lean_unbox(v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref_known(v___x_1050_, 1);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_a_1042_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1042_);
lean_ctor_set(v___x_1055_, 1, v___x_1050_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___boxed(lean_object* v_00_u03b9_1056_, lean_object* v_elem_1057_, lean_object* v_idx_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_p_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_Internal_Parsec_peekWhen_x3f(v_00_u03b9_1056_, v_elem_1057_, v_idx_1058_, v_inst_1059_, v_inst_1060_, v_inst_1061_, v_p_1062_, v_a_1063_);
lean_dec_ref(v_inst_1060_);
lean_dec_ref(v_inst_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___redArg(lean_object* v_inst_1065_, lean_object* v_it_1066_){
_start:
{
lean_object* v_hasNext_1067_; lean_object* v_curr_x27_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_hasNext_1067_ = lean_ctor_get(v_inst_1065_, 3);
lean_inc_ref(v_hasNext_1067_);
v_curr_x27_1068_ = lean_ctor_get(v_inst_1065_, 5);
lean_inc(v_curr_x27_1068_);
lean_dec_ref(v_inst_1065_);
lean_inc(v_it_1066_);
v___x_1069_ = lean_apply_1(v_hasNext_1067_, v_it_1066_);
v___x_1070_ = lean_unbox(v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v_curr_x27_1068_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_it_1066_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_inc(v_it_1066_);
v___x_1073_ = lean_apply_2(v_curr_x27_1068_, v_it_1066_, lean_box(0));
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_it_1066_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21(lean_object* v_00_u03b9_1075_, lean_object* v_elem_1076_, lean_object* v_idx_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_it_1081_){
_start:
{
lean_object* v_hasNext_1082_; lean_object* v_curr_x27_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_hasNext_1082_ = lean_ctor_get(v_inst_1080_, 3);
lean_inc_ref(v_hasNext_1082_);
v_curr_x27_1083_ = lean_ctor_get(v_inst_1080_, 5);
lean_inc(v_curr_x27_1083_);
lean_dec_ref(v_inst_1080_);
lean_inc(v_it_1081_);
v___x_1084_ = lean_apply_1(v_hasNext_1082_, v_it_1081_);
v___x_1085_ = lean_unbox(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v_curr_x27_1083_);
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_it_1081_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_inc(v_it_1081_);
v___x_1088_ = lean_apply_2(v_curr_x27_1083_, v_it_1081_, lean_box(0));
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_it_1081_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___boxed(lean_object* v_00_u03b9_1090_, lean_object* v_elem_1091_, lean_object* v_idx_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_it_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Internal_Parsec_peek_x21(v_00_u03b9_1090_, v_elem_1091_, v_idx_1092_, v_inst_1093_, v_inst_1094_, v_inst_1095_, v_it_1096_);
lean_dec_ref(v_inst_1094_);
lean_dec_ref(v_inst_1093_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___redArg(lean_object* v_inst_1098_, lean_object* v_default_1099_, lean_object* v_it_1100_){
_start:
{
lean_object* v_hasNext_1101_; lean_object* v_curr_x27_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_hasNext_1101_ = lean_ctor_get(v_inst_1098_, 3);
lean_inc_ref(v_hasNext_1101_);
v_curr_x27_1102_ = lean_ctor_get(v_inst_1098_, 5);
lean_inc(v_curr_x27_1102_);
lean_dec_ref(v_inst_1098_);
lean_inc(v_it_1100_);
v___x_1103_ = lean_apply_1(v_hasNext_1101_, v_it_1100_);
v___x_1104_ = lean_unbox(v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
lean_dec(v_curr_x27_1102_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_it_1100_);
lean_ctor_set(v___x_1105_, 1, v_default_1099_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec(v_default_1099_);
lean_inc(v_it_1100_);
v___x_1106_ = lean_apply_2(v_curr_x27_1102_, v_it_1100_, lean_box(0));
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_it_1100_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD(lean_object* v_00_u03b9_1108_, lean_object* v_elem_1109_, lean_object* v_idx_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_default_1114_, lean_object* v_it_1115_){
_start:
{
lean_object* v_hasNext_1116_; lean_object* v_curr_x27_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_hasNext_1116_ = lean_ctor_get(v_inst_1113_, 3);
lean_inc_ref(v_hasNext_1116_);
v_curr_x27_1117_ = lean_ctor_get(v_inst_1113_, 5);
lean_inc(v_curr_x27_1117_);
lean_dec_ref(v_inst_1113_);
lean_inc(v_it_1115_);
v___x_1118_ = lean_apply_1(v_hasNext_1116_, v_it_1115_);
v___x_1119_ = lean_unbox(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec(v_curr_x27_1117_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_it_1115_);
lean_ctor_set(v___x_1120_, 1, v_default_1114_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec(v_default_1114_);
lean_inc(v_it_1115_);
v___x_1121_ = lean_apply_2(v_curr_x27_1117_, v_it_1115_, lean_box(0));
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_it_1115_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___boxed(lean_object* v_00_u03b9_1123_, lean_object* v_elem_1124_, lean_object* v_idx_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_default_1129_, lean_object* v_it_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_Internal_Parsec_peekD(v_00_u03b9_1123_, v_elem_1124_, v_idx_1125_, v_inst_1126_, v_inst_1127_, v_inst_1128_, v_default_1129_, v_it_1130_);
lean_dec_ref(v_inst_1127_);
lean_dec_ref(v_inst_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___redArg(lean_object* v_inst_1132_, lean_object* v_it_1133_){
_start:
{
lean_object* v_hasNext_1134_; lean_object* v_next_x27_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_hasNext_1134_ = lean_ctor_get(v_inst_1132_, 3);
lean_inc_ref(v_hasNext_1134_);
v_next_x27_1135_ = lean_ctor_get(v_inst_1132_, 4);
lean_inc(v_next_x27_1135_);
lean_dec_ref(v_inst_1132_);
lean_inc(v_it_1133_);
v___x_1136_ = lean_apply_1(v_hasNext_1134_, v_it_1133_);
v___x_1137_ = lean_unbox(v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_next_x27_1135_);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_it_1133_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_apply_2(v_next_x27_1135_, v_it_1133_, lean_box(0));
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip(lean_object* v_00_u03b9_1143_, lean_object* v_elem_1144_, lean_object* v_idx_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_it_1149_){
_start:
{
lean_object* v_hasNext_1150_; lean_object* v_next_x27_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_hasNext_1150_ = lean_ctor_get(v_inst_1148_, 3);
lean_inc_ref(v_hasNext_1150_);
v_next_x27_1151_ = lean_ctor_get(v_inst_1148_, 4);
lean_inc(v_next_x27_1151_);
lean_dec_ref(v_inst_1148_);
lean_inc(v_it_1149_);
v___x_1152_ = lean_apply_1(v_hasNext_1150_, v_it_1149_);
v___x_1153_ = lean_unbox(v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_next_x27_1151_);
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_it_1149_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_apply_2(v_next_x27_1151_, v_it_1149_, lean_box(0));
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___boxed(lean_object* v_00_u03b9_1159_, lean_object* v_elem_1160_, lean_object* v_idx_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_it_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_Internal_Parsec_skip(v_00_u03b9_1159_, v_elem_1160_, v_idx_1161_, v_inst_1162_, v_inst_1163_, v_inst_1164_, v_it_1165_);
lean_dec_ref(v_inst_1163_);
lean_dec_ref(v_inst_1162_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___redArg(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_p_1169_, lean_object* v_acc_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1172_; 
lean_inc_ref(v_p_1169_);
lean_inc(v_a_1171_);
v___x_1172_ = lean_apply_1(v_p_1169_, v_a_1171_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_pos_1173_; lean_object* v_res_1174_; uint32_t v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_a_1171_);
v_pos_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_pos_1173_);
v_res_1174_ = lean_ctor_get(v___x_1172_, 1);
lean_inc(v_res_1174_);
lean_dec_ref_known(v___x_1172_, 2);
v___x_1175_ = lean_unbox_uint32(v_res_1174_);
lean_dec(v_res_1174_);
v___x_1176_ = lean_string_push(v_acc_1170_, v___x_1175_);
v_acc_1170_ = v___x_1176_;
v_a_1171_ = v_pos_1173_;
goto _start;
}
else
{
lean_object* v_pos_1178_; lean_object* v_err_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_p_1169_);
v_pos_1178_ = lean_ctor_get(v___x_1172_, 0);
v_err_1179_ = lean_ctor_get(v___x_1172_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1181_ = v___x_1172_;
v_isShared_1182_ = v_isSharedCheck_1194_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_err_1179_);
lean_inc(v_pos_1178_);
lean_dec(v___x_1172_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1194_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_pos_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_pos_1183_ = lean_ctor_get(v_inst_1168_, 0);
lean_inc_n(v_pos_1183_, 2);
lean_dec_ref(v_inst_1168_);
v___x_1184_ = lean_apply_1(v_pos_1183_, v_a_1171_);
lean_inc(v_pos_1178_);
v___x_1185_ = lean_apply_1(v_pos_1183_, v_pos_1178_);
v___x_1186_ = lean_apply_2(v_inst_1167_, v___x_1184_, v___x_1185_);
v___x_1187_ = lean_unbox(v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref(v_acc_1170_);
if (v_isShared_1182_ == 0)
{
v___x_1189_ = v___x_1181_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_pos_1178_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_err_1179_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
lean_object* v___x_1192_; 
lean_dec(v_err_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 0);
lean_ctor_set(v___x_1181_, 1, v_acc_1170_);
v___x_1192_ = v___x_1181_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_pos_1178_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_acc_1170_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore(lean_object* v_00_u03b9_1195_, lean_object* v_elem_1196_, lean_object* v_idx_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_p_1201_, lean_object* v_acc_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1198_, v_inst_1200_, v_p_1201_, v_acc_1202_, v_a_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___boxed(lean_object* v_00_u03b9_1205_, lean_object* v_elem_1206_, lean_object* v_idx_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_p_1211_, lean_object* v_acc_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_Internal_Parsec_manyCharsCore(v_00_u03b9_1205_, v_elem_1206_, v_idx_1207_, v_inst_1208_, v_inst_1209_, v_inst_1210_, v_p_1211_, v_acc_1212_, v_a_1213_);
lean_dec_ref(v_inst_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___redArg(lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_p_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0));
v___x_1220_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1215_, v_inst_1216_, v_p_1217_, v___x_1219_, v_a_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars(lean_object* v_00_u03b9_1221_, lean_object* v_elem_1222_, lean_object* v_idx_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_p_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0));
v___x_1230_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1224_, v_inst_1226_, v_p_1227_, v___x_1229_, v_a_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___boxed(lean_object* v_00_u03b9_1231_, lean_object* v_elem_1232_, lean_object* v_idx_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_p_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_Internal_Parsec_manyChars(v_00_u03b9_1231_, v_elem_1232_, v_idx_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_p_1237_, v_a_1238_);
lean_dec_ref(v_inst_1235_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___redArg(lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_p_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___x_1244_; 
lean_inc_ref(v_p_1242_);
v___x_1244_ = lean_apply_1(v_p_1242_, v_a_1243_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_pos_1245_; lean_object* v_res_1246_; lean_object* v___x_1247_; uint32_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_pos_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_pos_1245_);
v_res_1246_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_res_1246_);
lean_dec_ref_known(v___x_1244_, 2);
v___x_1247_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0));
v___x_1248_ = lean_unbox_uint32(v_res_1246_);
lean_dec(v_res_1246_);
v___x_1249_ = lean_string_push(v___x_1247_, v___x_1248_);
v___x_1250_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1240_, v_inst_1241_, v_p_1242_, v___x_1249_, v_pos_1245_);
return v___x_1250_;
}
else
{
lean_object* v_pos_1251_; lean_object* v_err_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_p_1242_);
lean_dec_ref(v_inst_1241_);
lean_dec_ref(v_inst_1240_);
v_pos_1251_ = lean_ctor_get(v___x_1244_, 0);
v_err_1252_ = lean_ctor_get(v___x_1244_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1244_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_err_1252_);
lean_inc(v_pos_1251_);
lean_dec(v___x_1244_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_pos_1251_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_err_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars(lean_object* v_00_u03b9_1260_, lean_object* v_elem_1261_, lean_object* v_idx_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_p_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v___x_1268_; 
lean_inc_ref(v_p_1266_);
v___x_1268_ = lean_apply_1(v_p_1266_, v_a_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_pos_1269_; lean_object* v_res_1270_; lean_object* v___x_1271_; uint32_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_pos_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_pos_1269_);
v_res_1270_ = lean_ctor_get(v___x_1268_, 1);
lean_inc(v_res_1270_);
lean_dec_ref_known(v___x_1268_, 2);
v___x_1271_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0));
v___x_1272_ = lean_unbox_uint32(v_res_1270_);
lean_dec(v_res_1270_);
v___x_1273_ = lean_string_push(v___x_1271_, v___x_1272_);
v___x_1274_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1263_, v_inst_1265_, v_p_1266_, v___x_1273_, v_pos_1269_);
return v___x_1274_;
}
else
{
lean_object* v_pos_1275_; lean_object* v_err_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_p_1266_);
lean_dec_ref(v_inst_1265_);
lean_dec_ref(v_inst_1263_);
v_pos_1275_ = lean_ctor_get(v___x_1268_, 0);
v_err_1276_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1268_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_err_1276_);
lean_inc(v_pos_1275_);
lean_dec(v___x_1268_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_pos_1275_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_err_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___boxed(lean_object* v_00_u03b9_1284_, lean_object* v_elem_1285_, lean_object* v_idx_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_p_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_Internal_Parsec_many1Chars(v_00_u03b9_1284_, v_elem_1285_, v_idx_1286_, v_inst_1287_, v_inst_1288_, v_inst_1289_, v_p_1290_, v_a_1291_);
lean_dec_ref(v_inst_1288_);
return v_res_1292_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Parsec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Parsec_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
