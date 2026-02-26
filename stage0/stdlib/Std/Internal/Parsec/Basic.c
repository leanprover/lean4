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
lean_object* lean_nat_to_int(lean_object*);
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_many___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_many___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_Parsec_many1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Parsec_many1___redArg___closed__0;
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
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_Error_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_Error_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_Parsec_Error_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_eof_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_eof_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_Parsec_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_other_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_Error_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_other_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_Parsec_Error_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instReprError_repr___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instReprError_repr___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprError_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1024u);
x_11 = lean_nat_dec_le(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
x_3 = x_12;
goto block_9;
}
else
{
lean_object* x_13; 
x_13 = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
x_3 = x_13;
goto block_9;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_26; uint8_t x_27; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_15 = x_1;
} else {
 lean_dec_ref(x_1);
 x_15 = lean_box(0);
}
x_26 = lean_unsigned_to_nat(1024u);
x_27 = lean_nat_dec_le(x_26, x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
x_16 = x_28;
goto block_25;
}
else
{
lean_object* x_29; 
x_29 = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
x_16 = x_29;
goto block_25;
}
block_25:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_17 = ((lean_object*)(l_Std_Internal_Parsec_instReprError_repr___closed__6));
x_18 = l_String_quote(x_14);
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(3, 1, 0);
} else {
 x_19 = x_15;
 lean_ctor_set_tag(x_19, 3);
}
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = 0;
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_Std_Internal_Parsec_instReprError_repr___closed__1));
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprError_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_instReprError_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instToStringError___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_Internal_Parsec_instToStringError___lam__0___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instToStringError___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_instToStringError___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_Parsec_ParseResult_ctorIdx___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_Parsec_ParseResult_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_Parsec_ParseResult_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_success_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_success_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_error_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_error_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_22; uint8_t x_23; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_22 = lean_unsigned_to_nat(1024u);
x_23 = lean_nat_dec_le(x_22, x_4);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
x_8 = x_24;
goto block_21;
}
else
{
lean_object* x_25; 
x_25 = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
x_8 = x_25;
goto block_21;
}
block_21:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_box(1);
x_10 = ((lean_object*)(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2));
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_apply_2(x_2, x_5, x_11);
if (lean_is_scalar(x_7)) {
 x_13 = lean_alloc_ctor(5, 2, 0);
} else {
 x_13 = x_7;
 lean_ctor_set_tag(x_13, 5);
}
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = lean_apply_2(x_1, x_6, x_11);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = 0;
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = l_Repr_addAppParen(x_19, x_4);
return x_20;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_43; uint8_t x_44; 
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_28 = x_3;
} else {
 lean_dec_ref(x_3);
 x_28 = lean_box(0);
}
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_4);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
x_29 = x_45;
goto block_42;
}
else
{
lean_object* x_46; 
x_46 = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
x_29 = x_46;
goto block_42;
}
block_42:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_box(1);
x_31 = ((lean_object*)(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5));
x_32 = lean_unsigned_to_nat(1024u);
x_33 = lean_apply_2(x_2, x_26, x_32);
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(5, 2, 0);
} else {
 x_34 = x_28;
 lean_ctor_set_tag(x_34, 5);
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_36 = l_Std_Internal_Parsec_instReprError_repr(x_27, x_32);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
x_39 = 0;
x_40 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = l_Repr_addAppParen(x_40, x_4);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_Parsec_instReprParseResult_repr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instReprParseResult_repr___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instReprParseResult_repr___boxed), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___closed__0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_apply_2(x_2, x_6, x_5);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec_ref(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_1(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_2(x_5, x_9, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec_ref(x_5);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_6);
x_7 = lean_apply_1(x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_2(x_4, x_9, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec_ref(x_4);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec_ref(x_2);
lean_inc(x_14);
x_15 = lean_apply_1(x_14, x_6);
lean_inc(x_12);
x_16 = lean_apply_1(x_14, x_12);
x_17 = lean_apply_2(x_1, x_15, x_16);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_5);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_5, x_19, x_12);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec_ref(x_2);
lean_inc(x_23);
x_24 = lean_apply_1(x_23, x_6);
lean_inc(x_21);
x_25 = lean_apply_1(x_23, x_21);
x_26 = lean_apply_2(x_1, x_24, x_25);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_apply_2(x_5, x_29, x_21);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_12);
x_13 = lean_apply_1(x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_apply_2(x_10, x_15, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_10);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec_ref(x_7);
lean_inc(x_20);
x_21 = lean_apply_1(x_20, x_12);
lean_inc(x_18);
x_22 = lean_apply_1(x_20, x_18);
x_23 = lean_apply_2(x_5, x_21, x_22);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_11);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_13);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_11, x_25, x_18);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
lean_dec_ref(x_7);
lean_inc(x_29);
x_30 = lean_apply_1(x_29, x_12);
lean_inc(x_27);
x_31 = lean_apply_1(x_29, x_27);
x_32 = lean_apply_2(x_5, x_30, x_31);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_apply_2(x_11, x_35, x_27);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Internal_Parsec_tryCatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_apply_1(x_3, x_8);
lean_ctor_set(x_6, 1, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_apply_1(x_3, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_dec(x_8);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_apply_1(x_8, x_12);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_apply_1(x_8, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec_ref(x_4);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_dec(x_12);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_dec_ref(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_4, x_8, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec_ref(x_4);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_Internal_Parsec_instMonad___closed__9));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc(x_8);
x_9 = lean_apply_1(x_8, x_5);
lean_inc(x_7);
x_10 = lean_apply_1(x_8, x_7);
x_11 = lean_apply_2(x_1, x_9, x_10);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_4);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_6);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_4, x_13, x_7);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_10);
x_11 = lean_apply_1(x_8, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec_ref(x_7);
lean_inc(x_13);
x_14 = lean_apply_1(x_13, x_10);
lean_inc(x_12);
x_15 = lean_apply_1(x_13, x_12);
x_16 = lean_apply_2(x_5, x_14, x_15);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_9);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_11);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_9, x_18, x_12);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Internal_Parsec_orElse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
x_5 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_6);
x_7 = lean_apply_1(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
lean_inc(x_9);
x_10 = lean_apply_1(x_9, x_6);
lean_inc(x_8);
x_11 = lean_apply_1(x_9, x_8);
x_12 = lean_apply_2(x_2, x_10, x_11);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_5);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_7);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_5, x_14, x_8);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = ((lean_object*)(l_Std_Internal_Parsec_instAlternative___redArg___closed__0));
x_4 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___redArg___lam__1), 6, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = ((lean_object*)(l_Std_Internal_Parsec_instMonad___closed__7));
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Std_Internal_Parsec_instAlternative___redArg___closed__0));
x_8 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___redArg___lam__1), 6, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_4);
x_9 = ((lean_object*)(l_Std_Internal_Parsec_instMonad___closed__7));
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Internal_Parsec_instAlternative(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = ((lean_object*)(l_Std_Internal_Parsec_eof___redArg___closed__1));
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = lean_apply_1(x_8, x_7);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = ((lean_object*)(l_Std_Internal_Parsec_eof___redArg___closed__1));
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_Parsec_eof(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = lean_apply_1(x_8, x_7);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_Parsec_isEof(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_array_push(x_4, x_8);
x_4 = x_9;
x_5 = x_7;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec_ref(x_3);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec_ref(x_2);
lean_inc(x_14);
x_15 = lean_apply_1(x_14, x_5);
lean_inc(x_12);
x_16 = lean_apply_1(x_14, x_12);
x_17 = lean_apply_2(x_1, x_15, x_16);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_4);
return x_6;
}
else
{
lean_dec(x_13);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec_ref(x_2);
lean_inc(x_21);
x_22 = lean_apply_1(x_21, x_5);
lean_inc(x_19);
x_23 = lean_apply_1(x_21, x_19);
x_24 = lean_apply_2(x_1, x_22, x_23);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_4);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Internal_Parsec_manyCore___redArg(x_5, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Internal_Parsec_manyCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_6);
return x_11;
}
}
static lean_object* _init_l_Std_Internal_Parsec_many___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_obj_once(&l_Std_Internal_Parsec_many___redArg___closed__0, &l_Std_Internal_Parsec_many___redArg___closed__0_once, _init_l_Std_Internal_Parsec_many___redArg___closed__0);
x_6 = l_Std_Internal_Parsec_manyCore___redArg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_Std_Internal_Parsec_many___redArg___closed__0, &l_Std_Internal_Parsec_many___redArg___closed__0_once, _init_l_Std_Internal_Parsec_many___redArg___closed__0);
x_11 = l_Std_Internal_Parsec_manyCore___redArg(x_5, x_7, x_8, x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Internal_Parsec_many(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_6);
return x_10;
}
}
static lean_object* _init_l_Std_Internal_Parsec_many1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_3);
x_5 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_obj_once(&l_Std_Internal_Parsec_many1___redArg___closed__0, &l_Std_Internal_Parsec_many1___redArg___closed__0_once, _init_l_Std_Internal_Parsec_many1___redArg___closed__0);
x_9 = lean_array_push(x_8, x_7);
x_10 = l_Std_Internal_Parsec_manyCore___redArg(x_1, x_2, x_3, x_9, x_6);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc_ref(x_8);
x_10 = lean_apply_1(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_obj_once(&l_Std_Internal_Parsec_many1___redArg___closed__0, &l_Std_Internal_Parsec_many1___redArg___closed__0_once, _init_l_Std_Internal_Parsec_many1___redArg___closed__0);
x_14 = lean_array_push(x_13, x_12);
x_15 = l_Std_Internal_Parsec_manyCore___redArg(x_5, x_7, x_8, x_14, x_11);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Internal_Parsec_many1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc(x_2);
x_6 = lean_apply_1(x_3, x_2);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_10 = lean_apply_2(x_5, x_2, lean_box(0));
x_11 = lean_apply_2(x_4, x_2, lean_box(0));
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 5);
lean_inc(x_10);
lean_dec_ref(x_6);
lean_inc(x_7);
x_11 = lean_apply_1(x_8, x_7);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_7);
x_15 = lean_apply_2(x_10, x_7, lean_box(0));
x_16 = lean_apply_2(x_9, x_7, lean_box(0));
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_Parsec_any(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 5);
lean_inc(x_6);
lean_dec_ref(x_1);
lean_inc(x_3);
x_7 = lean_apply_1(x_4, x_3);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_3);
x_11 = lean_apply_2(x_6, x_3, lean_box(0));
lean_inc(x_3);
x_12 = lean_apply_2(x_5, x_3, lean_box(0));
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_apply_1(x_2, x_11);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_13);
x_16 = ((lean_object*)(l_Std_Internal_Parsec_satisfy___redArg___closed__1));
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_dec(x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 5);
lean_inc(x_11);
lean_dec_ref(x_6);
lean_inc(x_8);
x_12 = lean_apply_1(x_9, x_8);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_8);
x_16 = lean_apply_2(x_11, x_8, lean_box(0));
lean_inc(x_8);
x_17 = lean_apply_2(x_10, x_8, lean_box(0));
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_apply_1(x_7, x_16);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_18);
x_21 = ((lean_object*)(l_Std_Internal_Parsec_satisfy___redArg___closed__1));
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_dec(x_8);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_Parsec_satisfy(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
x_5 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__1));
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec_ref(x_1);
lean_inc(x_2);
x_5 = lean_apply_1(x_3, x_2);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_9 = lean_apply_2(x_4, x_2, lean_box(0));
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
lean_dec_ref(x_6);
lean_inc(x_7);
x_10 = lean_apply_1(x_8, x_7);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_7);
x_14 = lean_apply_2(x_9, x_7, lean_box(0));
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_Parsec_peek_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc(x_3);
x_6 = lean_apply_1(x_4, x_3);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_10 = lean_apply_2(x_5, x_3, lean_box(0));
lean_inc(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_apply_1(x_2, x_10);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 5);
lean_inc(x_10);
lean_dec_ref(x_6);
lean_inc(x_8);
x_11 = lean_apply_1(x_9, x_8);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_8);
x_15 = lean_apply_2(x_10, x_8, lean_box(0));
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_apply_1(x_7, x_15);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_Parsec_peekWhen_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec_ref(x_1);
lean_inc(x_2);
x_5 = lean_apply_1(x_3, x_2);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
x_9 = lean_apply_2(x_4, x_2, lean_box(0));
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
lean_dec_ref(x_6);
lean_inc(x_7);
x_10 = lean_apply_1(x_8, x_7);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_7);
x_14 = lean_apply_2(x_9, x_7, lean_box(0));
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_Parsec_peek_x21(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc(x_3);
x_6 = lean_apply_1(x_4, x_3);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_inc(x_3);
x_9 = lean_apply_2(x_5, x_3, lean_box(0));
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 5);
lean_inc(x_10);
lean_dec_ref(x_6);
lean_inc(x_8);
x_11 = lean_apply_1(x_9, x_8);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_inc(x_8);
x_14 = lean_apply_2(x_10, x_8, lean_box(0));
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_Parsec_peekD(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec_ref(x_1);
lean_inc(x_2);
x_5 = lean_apply_1(x_3, x_2);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_apply_2(x_4, x_2, lean_box(0));
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 4);
lean_inc(x_9);
lean_dec_ref(x_6);
lean_inc(x_7);
x_10 = lean_apply_1(x_8, x_7);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_apply_2(x_9, x_7, lean_box(0));
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_Parsec_skip(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unbox_uint32(x_8);
lean_dec(x_8);
x_10 = lean_string_push(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_3);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec_ref(x_2);
lean_inc(x_15);
x_16 = lean_apply_1(x_15, x_5);
lean_inc(x_13);
x_17 = lean_apply_1(x_15, x_13);
x_18 = lean_apply_2(x_1, x_16, x_17);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_4);
return x_6;
}
else
{
lean_dec(x_14);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec_ref(x_2);
lean_inc(x_22);
x_23 = lean_apply_1(x_22, x_5);
lean_inc(x_20);
x_24 = lean_apply_1(x_22, x_20);
x_25 = lean_apply_2(x_1, x_23, x_24);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec_ref(x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Internal_Parsec_manyCharsCore___redArg(x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Internal_Parsec_manyCharsCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0));
x_6 = l_Std_Internal_Parsec_manyCharsCore___redArg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0));
x_10 = l_Std_Internal_Parsec_manyCharsCore___redArg(x_4, x_6, x_7, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_Parsec_manyChars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_3);
x_5 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0));
x_9 = lean_unbox_uint32(x_7);
lean_dec(x_7);
x_10 = lean_string_push(x_8, x_9);
x_11 = l_Std_Internal_Parsec_manyCharsCore___redArg(x_1, x_2, x_3, x_10, x_6);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_7);
x_9 = lean_apply_1(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___lam__0___closed__0));
x_13 = lean_unbox_uint32(x_11);
lean_dec(x_11);
x_14 = lean_string_push(x_12, x_13);
x_15 = l_Std_Internal_Parsec_manyCharsCore___redArg(x_4, x_6, x_7, x_14, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Internal_Parsec_many1Chars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
return x_9;
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
