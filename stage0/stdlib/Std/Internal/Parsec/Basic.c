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
static const lean_string_object l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_instInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instInhabited___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instInhabited___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instInhabited___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_instMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__0_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__1_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__2 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__2_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___redArg___lam__3, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__3 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__3_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___redArg___lam__4, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__4 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__4_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_instMonad___redArg___lam__5, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__5 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__5_value;
static const lean_ctor_object l_Std_Internal_Parsec_instMonad___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__0_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__6 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__6_value;
static const lean_ctor_object l_Std_Internal_Parsec_instMonad___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__6_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__2_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__3_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__4_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__5_value)}};
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__7 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__7_value;
static const lean_closure_object l_Std_Internal_Parsec_instMonad___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_bind, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__8 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__8_value;
static const lean_ctor_object l_Std_Internal_Parsec_instMonad___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__7_value),((lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__8_value)}};
static const lean_object* l_Std_Internal_Parsec_instMonad___redArg___closed__9 = (const lean_object*)&l_Std_Internal_Parsec_instMonad___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg___lam__0(lean_object* v_it_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1));
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v_it_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg(){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___closed__0));
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg___boxed(lean_object* v___dummy_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Internal_Parsec_instInhabited___redArg();
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited(lean_object* v_00_u03b1_258_, lean_object* v_00_u03b9_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___closed__0));
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure___redArg(lean_object* v_a_261_, lean_object* v_it_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v_it_262_);
lean_ctor_set(v___x_263_, 1, v_a_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure(lean_object* v_00_u03b1_264_, lean_object* v_00_u03b9_265_, lean_object* v_a_266_, lean_object* v_it_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_it_267_);
lean_ctor_set(v___x_268_, 1, v_a_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind___redArg(lean_object* v_f_269_, lean_object* v_g_270_, lean_object* v_it_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_apply_1(v_f_269_, v_it_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_pos_273_; lean_object* v_res_274_; lean_object* v___x_275_; 
v_pos_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_pos_273_);
v_res_274_ = lean_ctor_get(v___x_272_, 1);
lean_inc(v_res_274_);
lean_dec_ref_known(v___x_272_, 2);
v___x_275_ = lean_apply_2(v_g_270_, v_res_274_, v_pos_273_);
return v___x_275_;
}
else
{
lean_object* v_pos_276_; lean_object* v_err_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec_ref(v_g_270_);
v_pos_276_ = lean_ctor_get(v___x_272_, 0);
v_err_277_ = lean_ctor_get(v___x_272_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_272_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_err_277_);
lean_inc(v_pos_276_);
lean_dec(v___x_272_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_pos_276_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_err_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind(lean_object* v_00_u03b9_285_, lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_f_288_, lean_object* v_g_289_, lean_object* v_it_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_apply_1(v_f_288_, v_it_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_pos_292_; lean_object* v_res_293_; lean_object* v___x_294_; 
v_pos_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_pos_292_);
v_res_293_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_res_293_);
lean_dec_ref_known(v___x_291_, 2);
v___x_294_ = lean_apply_2(v_g_289_, v_res_293_, v_pos_292_);
return v___x_294_;
}
else
{
lean_object* v_pos_295_; lean_object* v_err_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref(v_g_289_);
v_pos_295_ = lean_ctor_get(v___x_291_, 0);
v_err_296_ = lean_ctor_get(v___x_291_, 1);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_291_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_err_296_);
lean_inc(v_pos_295_);
lean_dec(v___x_291_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_pos_295_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_err_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail___redArg(lean_object* v_msg_304_, lean_object* v_it_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v_msg_304_);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v_it_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b9_309_, lean_object* v_msg_310_, lean_object* v_it_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_msg_310_);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v_it_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___redArg(lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_p_316_, lean_object* v_csuccess_317_, lean_object* v_cerror_318_, lean_object* v_it_319_){
_start:
{
lean_object* v___x_320_; 
lean_inc(v_it_319_);
v___x_320_ = lean_apply_1(v_p_316_, v_it_319_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_pos_321_; lean_object* v_res_322_; lean_object* v___x_323_; 
lean_dec(v_it_319_);
lean_dec_ref(v_cerror_318_);
lean_dec_ref(v_inst_315_);
lean_dec_ref(v_inst_314_);
v_pos_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_pos_321_);
v_res_322_ = lean_ctor_get(v___x_320_, 1);
lean_inc(v_res_322_);
lean_dec_ref_known(v___x_320_, 2);
v___x_323_ = lean_apply_2(v_csuccess_317_, v_res_322_, v_pos_321_);
return v___x_323_;
}
else
{
lean_object* v_pos_324_; lean_object* v_err_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v_csuccess_317_);
v_pos_324_ = lean_ctor_get(v___x_320_, 0);
v_err_325_ = lean_ctor_get(v___x_320_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_339_ == 0)
{
v___x_327_ = v___x_320_;
v_isShared_328_ = v_isSharedCheck_339_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_err_325_);
lean_inc(v_pos_324_);
lean_dec(v___x_320_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_339_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_pos_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_pos_329_ = lean_ctor_get(v_inst_315_, 0);
lean_inc_n(v_pos_329_, 2);
lean_dec_ref(v_inst_315_);
v___x_330_ = lean_apply_1(v_pos_329_, v_it_319_);
lean_inc(v_pos_324_);
v___x_331_ = lean_apply_1(v_pos_329_, v_pos_324_);
v___x_332_ = lean_apply_2(v_inst_314_, v___x_330_, v___x_331_);
v___x_333_ = lean_unbox(v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_335_; 
lean_dec_ref(v_cerror_318_);
if (v_isShared_328_ == 0)
{
v___x_335_ = v___x_327_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_pos_324_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_err_325_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_del_object(v___x_327_);
lean_dec(v_err_325_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_apply_2(v_cerror_318_, v___x_337_, v_pos_324_);
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch(lean_object* v_00_u03b1_340_, lean_object* v_00_u03b9_341_, lean_object* v_elem_342_, lean_object* v_idx_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_00_u03b2_347_, lean_object* v_p_348_, lean_object* v_csuccess_349_, lean_object* v_cerror_350_, lean_object* v_it_351_){
_start:
{
lean_object* v___x_352_; 
lean_inc(v_it_351_);
v___x_352_ = lean_apply_1(v_p_348_, v_it_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_pos_353_; lean_object* v_res_354_; lean_object* v___x_355_; 
lean_dec(v_it_351_);
lean_dec_ref(v_cerror_350_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_344_);
v_pos_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_pos_353_);
v_res_354_ = lean_ctor_get(v___x_352_, 1);
lean_inc(v_res_354_);
lean_dec_ref_known(v___x_352_, 2);
v___x_355_ = lean_apply_2(v_csuccess_349_, v_res_354_, v_pos_353_);
return v___x_355_;
}
else
{
lean_object* v_pos_356_; lean_object* v_err_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v_csuccess_349_);
v_pos_356_ = lean_ctor_get(v___x_352_, 0);
v_err_357_ = lean_ctor_get(v___x_352_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_371_ == 0)
{
v___x_359_ = v___x_352_;
v_isShared_360_ = v_isSharedCheck_371_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_err_357_);
lean_inc(v_pos_356_);
lean_dec(v___x_352_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_371_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_pos_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_pos_361_ = lean_ctor_get(v_inst_346_, 0);
lean_inc_n(v_pos_361_, 2);
lean_dec_ref(v_inst_346_);
v___x_362_ = lean_apply_1(v_pos_361_, v_it_351_);
lean_inc(v_pos_356_);
v___x_363_ = lean_apply_1(v_pos_361_, v_pos_356_);
v___x_364_ = lean_apply_2(v_inst_344_, v___x_362_, v___x_363_);
v___x_365_ = lean_unbox(v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_367_; 
lean_dec_ref(v_cerror_350_);
if (v_isShared_360_ == 0)
{
v___x_367_ = v___x_359_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_pos_356_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_err_357_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_del_object(v___x_359_);
lean_dec(v_err_357_);
v___x_369_ = lean_box(0);
v___x_370_ = lean_apply_2(v_cerror_350_, v___x_369_, v_pos_356_);
return v___x_370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___boxed(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b9_373_, lean_object* v_elem_374_, lean_object* v_idx_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_00_u03b2_379_, lean_object* v_p_380_, lean_object* v_csuccess_381_, lean_object* v_cerror_382_, lean_object* v_it_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Internal_Parsec_tryCatch(v_00_u03b1_372_, v_00_u03b9_373_, v_elem_374_, v_idx_375_, v_inst_376_, v_inst_377_, v_inst_378_, v_00_u03b2_379_, v_p_380_, v_csuccess_381_, v_cerror_382_, v_it_383_);
lean_dec_ref(v_inst_377_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__0(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_f_387_, lean_object* v_x_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_apply_1(v_x_388_, v___y_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_pos_391_; lean_object* v_res_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_pos_391_ = lean_ctor_get(v___x_390_, 0);
v_res_392_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_400_ == 0)
{
v___x_394_ = v___x_390_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_res_392_);
lean_inc(v_pos_391_);
lean_dec(v___x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = lean_apply_1(v_f_387_, v_res_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_pos_391_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v_pos_401_; lean_object* v_err_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_f_387_);
v_pos_401_ = lean_ctor_get(v___x_390_, 0);
v_err_402_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_390_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_err_402_);
lean_inc(v_pos_401_);
lean_dec(v___x_390_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_pos_401_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_err_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__1(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_apply_1(v___y_413_, v___y_414_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_pos_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_pos_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_415_, 1);
lean_dec(v_unused_424_);
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_pos_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v___y_412_);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_pos_416_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___y_412_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_pos_425_; lean_object* v_err_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v___y_412_);
v_pos_425_ = lean_ctor_get(v___x_415_, 0);
v_err_426_ = lean_ctor_get(v___x_415_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_415_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_err_426_);
lean_inc(v_pos_425_);
lean_dec(v___x_415_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_pos_425_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_err_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__2(lean_object* v_00_u03b1_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v___y_436_);
lean_ctor_set(v___x_437_, 1, v___y_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__3(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_f_440_, lean_object* v_x_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_apply_1(v_f_440_, v___y_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_pos_444_; lean_object* v_res_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_pos_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_pos_444_);
v_res_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_res_445_);
lean_dec_ref_known(v___x_443_, 2);
v___x_446_ = lean_box(0);
v___x_447_ = lean_apply_2(v_x_441_, v___x_446_, v_pos_444_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_pos_448_; lean_object* v_res_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_pos_448_ = lean_ctor_get(v___x_447_, 0);
v_res_449_ = lean_ctor_get(v___x_447_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_457_ == 0)
{
v___x_451_ = v___x_447_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_res_449_);
lean_inc(v_pos_448_);
lean_dec(v___x_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_apply_1(v_res_445_, v_res_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_pos_448_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_pos_458_; lean_object* v_err_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_res_445_);
v_pos_458_ = lean_ctor_get(v___x_447_, 0);
v_err_459_ = lean_ctor_get(v___x_447_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_447_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_err_459_);
lean_inc(v_pos_458_);
lean_dec(v___x_447_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_pos_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_err_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_pos_467_; lean_object* v_err_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v_x_441_);
v_pos_467_ = lean_ctor_get(v___x_443_, 0);
v_err_468_ = lean_ctor_get(v___x_443_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_443_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_err_468_);
lean_inc(v_pos_467_);
lean_dec(v___x_443_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_pos_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_err_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__4(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = lean_apply_1(v_x_478_, v___y_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_pos_482_; lean_object* v_res_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_pos_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_pos_482_);
v_res_483_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_res_483_);
lean_dec_ref_known(v___x_481_, 2);
v___x_484_ = lean_box(0);
v___x_485_ = lean_apply_2(v_y_479_, v___x_484_, v_pos_482_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_pos_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_pos_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v___x_485_, 1);
lean_dec(v_unused_494_);
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_pos_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v_res_483_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_pos_486_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_res_483_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
lean_object* v_pos_495_; lean_object* v_err_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_res_483_);
v_pos_495_ = lean_ctor_get(v___x_485_, 0);
v_err_496_ = lean_ctor_get(v___x_485_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_485_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_err_496_);
lean_inc(v_pos_495_);
lean_dec(v___x_485_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_pos_495_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_err_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_dec_ref(v_y_479_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__5(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_x_506_, lean_object* v_y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_apply_1(v_x_506_, v___y_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_pos_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_pos_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_pos_510_);
lean_dec_ref_known(v___x_509_, 2);
v___x_511_ = lean_box(0);
v___x_512_ = lean_apply_2(v_y_507_, v___x_511_, v_pos_510_);
return v___x_512_;
}
else
{
lean_object* v_pos_513_; lean_object* v_err_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v_y_507_);
v_pos_513_ = lean_ctor_get(v___x_509_, 0);
v_err_514_ = lean_ctor_get(v___x_509_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_509_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_err_514_);
lean_inc(v_pos_513_);
lean_dec(v___x_509_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_pos_513_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_err_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg(){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___redArg___closed__9));
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___boxed(lean_object* v___dummy_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_Internal_Parsec_instMonad___redArg();
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad(lean_object* v_00_u03b9_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___redArg___closed__9));
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___redArg(lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_p_549_, lean_object* v_q_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_552_; 
lean_inc(v_a_551_);
v___x_552_ = lean_apply_1(v_p_549_, v_a_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_dec(v_a_551_);
lean_dec_ref(v_q_550_);
lean_dec_ref(v_inst_548_);
lean_dec_ref(v_inst_547_);
return v___x_552_;
}
else
{
lean_object* v_pos_553_; lean_object* v_pos_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_pos_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc_n(v_pos_553_, 2);
v_pos_554_ = lean_ctor_get(v_inst_548_, 0);
lean_inc_n(v_pos_554_, 2);
lean_dec_ref(v_inst_548_);
v___x_555_ = lean_apply_1(v_pos_554_, v_a_551_);
v___x_556_ = lean_apply_1(v_pos_554_, v_pos_553_);
v___x_557_ = lean_apply_2(v_inst_547_, v___x_555_, v___x_556_);
v___x_558_ = lean_unbox(v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v_pos_553_);
lean_dec_ref(v_q_550_);
return v___x_552_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref_known(v___x_552_, 2);
v___x_559_ = lean_box(0);
v___x_560_ = lean_apply_2(v_q_550_, v___x_559_, v_pos_553_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b9_562_, lean_object* v_elem_563_, lean_object* v_idx_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_p_568_, lean_object* v_q_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; 
lean_inc(v_a_570_);
v___x_571_ = lean_apply_1(v_p_568_, v_a_570_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_dec(v_a_570_);
lean_dec_ref(v_q_569_);
lean_dec_ref(v_inst_567_);
lean_dec_ref(v_inst_565_);
return v___x_571_;
}
else
{
lean_object* v_pos_572_; lean_object* v_pos_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_pos_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_n(v_pos_572_, 2);
v_pos_573_ = lean_ctor_get(v_inst_567_, 0);
lean_inc_n(v_pos_573_, 2);
lean_dec_ref(v_inst_567_);
v___x_574_ = lean_apply_1(v_pos_573_, v_a_570_);
v___x_575_ = lean_apply_1(v_pos_573_, v_pos_572_);
v___x_576_ = lean_apply_2(v_inst_565_, v___x_574_, v___x_575_);
v___x_577_ = lean_unbox(v___x_576_);
if (v___x_577_ == 0)
{
lean_dec(v_pos_572_);
lean_dec_ref(v_q_569_);
return v___x_571_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref_known(v___x_571_, 2);
v___x_578_ = lean_box(0);
v___x_579_ = lean_apply_2(v_q_569_, v___x_578_, v_pos_572_);
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___boxed(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b9_581_, lean_object* v_elem_582_, lean_object* v_idx_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_p_587_, lean_object* v_q_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_Internal_Parsec_orElse(v_00_u03b1_580_, v_00_u03b9_581_, v_elem_582_, v_idx_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_p_587_, v_q_588_, v_a_589_);
lean_dec_ref(v_inst_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt___redArg(lean_object* v_p_591_, lean_object* v_it_592_){
_start:
{
lean_object* v___x_593_; 
lean_inc(v_it_592_);
v___x_593_ = lean_apply_1(v_p_591_, v_it_592_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_dec(v_it_592_);
return v___x_593_;
}
else
{
lean_object* v_err_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_err_594_ = lean_ctor_get(v___x_593_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_602_);
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_err_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v_it_592_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_it_592_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_err_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b9_604_, lean_object* v_p_605_, lean_object* v_it_606_){
_start:
{
lean_object* v___x_607_; 
lean_inc(v_it_606_);
v___x_607_ = lean_apply_1(v_p_605_, v_it_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_dec(v_it_606_);
return v___x_607_;
}
else
{
lean_object* v_err_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_err_608_ = lean_ctor_get(v___x_607_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_607_, 0);
lean_dec(v_unused_616_);
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_err_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_it_606_);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_it_606_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_err_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__0(lean_object* v_00_u03b1_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1));
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v___y_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__1(lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_00_u03b1_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_627_; 
lean_inc(v___y_626_);
v___x_627_ = lean_apply_1(v___y_624_, v___y_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec_ref(v_inst_622_);
lean_dec_ref(v_inst_621_);
return v___x_627_;
}
else
{
lean_object* v_pos_628_; lean_object* v_pos_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_pos_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_n(v_pos_628_, 2);
v_pos_629_ = lean_ctor_get(v_inst_621_, 0);
lean_inc_n(v_pos_629_, 2);
lean_dec_ref(v_inst_621_);
v___x_630_ = lean_apply_1(v_pos_629_, v___y_626_);
v___x_631_ = lean_apply_1(v_pos_629_, v_pos_628_);
v___x_632_ = lean_apply_2(v_inst_622_, v___x_630_, v___x_631_);
v___x_633_ = lean_unbox(v___x_632_);
if (v___x_633_ == 0)
{
lean_dec(v_pos_628_);
lean_dec_ref(v___y_625_);
return v___x_627_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref_known(v___x_627_, 2);
v___x_634_ = lean_box(0);
v___x_635_ = lean_apply_2(v___y_625_, v___x_634_, v_pos_628_);
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg(lean_object* v_inst_637_, lean_object* v_inst_638_){
_start:
{
lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___f_639_ = ((lean_object*)(l_Std_Internal_Parsec_instAlternative___redArg___closed__0));
v___f_640_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___redArg___lam__1), 6, 2);
lean_closure_set(v___f_640_, 0, v_inst_638_);
lean_closure_set(v___f_640_, 1, v_inst_637_);
v___x_641_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___redArg___closed__7));
v___x_642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___f_639_);
lean_ctor_set(v___x_642_, 2, v___f_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative(lean_object* v_00_u03b9_643_, lean_object* v_elem_644_, lean_object* v_idx_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_){
_start:
{
lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___f_649_ = ((lean_object*)(l_Std_Internal_Parsec_instAlternative___redArg___closed__0));
v___f_650_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___redArg___lam__1), 6, 2);
lean_closure_set(v___f_650_, 0, v_inst_648_);
lean_closure_set(v___f_650_, 1, v_inst_646_);
v___x_651_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___redArg___closed__7));
v___x_652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___f_649_);
lean_ctor_set(v___x_652_, 2, v___f_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___boxed(lean_object* v_00_u03b9_653_, lean_object* v_elem_654_, lean_object* v_idx_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Internal_Parsec_instAlternative(v_00_u03b9_653_, v_elem_654_, v_idx_655_, v_inst_656_, v_inst_657_, v_inst_658_);
lean_dec_ref(v_inst_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___redArg(lean_object* v_inst_663_, lean_object* v_it_664_){
_start:
{
lean_object* v_hasNext_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_hasNext_665_ = lean_ctor_get(v_inst_663_, 3);
lean_inc_ref(v_hasNext_665_);
lean_dec_ref(v_inst_663_);
lean_inc(v_it_664_);
v___x_666_ = lean_apply_1(v_hasNext_665_, v_it_664_);
v___x_667_ = lean_unbox(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_box(0);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_it_664_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Std_Internal_Parsec_eof___redArg___closed__1));
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v_it_664_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof(lean_object* v_00_u03b9_672_, lean_object* v_elem_673_, lean_object* v_idx_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_it_678_){
_start:
{
lean_object* v_hasNext_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_hasNext_679_ = lean_ctor_get(v_inst_677_, 3);
lean_inc_ref(v_hasNext_679_);
lean_dec_ref(v_inst_677_);
lean_inc(v_it_678_);
v___x_680_ = lean_apply_1(v_hasNext_679_, v_it_678_);
v___x_681_ = lean_unbox(v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_box(0);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_it_678_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Std_Internal_Parsec_eof___redArg___closed__1));
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v_it_678_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___boxed(lean_object* v_00_u03b9_686_, lean_object* v_elem_687_, lean_object* v_idx_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_it_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Internal_Parsec_eof(v_00_u03b9_686_, v_elem_687_, v_idx_688_, v_inst_689_, v_inst_690_, v_inst_691_, v_it_692_);
lean_dec_ref(v_inst_690_);
lean_dec_ref(v_inst_689_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___redArg(lean_object* v_inst_694_, lean_object* v_it_695_){
_start:
{
lean_object* v_hasNext_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_hasNext_696_ = lean_ctor_get(v_inst_694_, 3);
lean_inc_ref(v_hasNext_696_);
lean_dec_ref(v_inst_694_);
lean_inc(v_it_695_);
v___x_697_ = lean_apply_1(v_hasNext_696_, v_it_695_);
v___x_698_ = lean_unbox(v___x_697_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = 1;
v___x_700_ = lean_box(v___x_699_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_it_695_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
return v___x_701_;
}
else
{
uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = 0;
v___x_703_ = lean_box(v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_it_695_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof(lean_object* v_00_u03b9_705_, lean_object* v_elem_706_, lean_object* v_idx_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_it_711_){
_start:
{
lean_object* v_hasNext_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_hasNext_712_ = lean_ctor_get(v_inst_710_, 3);
lean_inc_ref(v_hasNext_712_);
lean_dec_ref(v_inst_710_);
lean_inc(v_it_711_);
v___x_713_ = lean_apply_1(v_hasNext_712_, v_it_711_);
v___x_714_ = lean_unbox(v___x_713_);
if (v___x_714_ == 0)
{
uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = 1;
v___x_716_ = lean_box(v___x_715_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v_it_711_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
return v___x_717_;
}
else
{
uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = 0;
v___x_719_ = lean_box(v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_it_711_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___boxed(lean_object* v_00_u03b9_721_, lean_object* v_elem_722_, lean_object* v_idx_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_it_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_Internal_Parsec_isEof(v_00_u03b9_721_, v_elem_722_, v_idx_723_, v_inst_724_, v_inst_725_, v_inst_726_, v_it_727_);
lean_dec_ref(v_inst_725_);
lean_dec_ref(v_inst_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___redArg(lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_p_731_, lean_object* v_acc_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; 
lean_inc_ref(v_p_731_);
lean_inc(v_a_733_);
v___x_734_ = lean_apply_1(v_p_731_, v_a_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_pos_735_; lean_object* v_res_736_; lean_object* v___x_737_; 
lean_dec(v_a_733_);
v_pos_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_pos_735_);
v_res_736_ = lean_ctor_get(v___x_734_, 1);
lean_inc(v_res_736_);
lean_dec_ref_known(v___x_734_, 2);
v___x_737_ = lean_array_push(v_acc_732_, v_res_736_);
v_acc_732_ = v___x_737_;
v_a_733_ = v_pos_735_;
goto _start;
}
else
{
lean_object* v_pos_739_; lean_object* v_err_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v_p_731_);
v_pos_739_ = lean_ctor_get(v___x_734_, 0);
v_err_740_ = lean_ctor_get(v___x_734_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_755_ == 0)
{
v___x_742_ = v___x_734_;
v_isShared_743_ = v_isSharedCheck_755_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_err_740_);
lean_inc(v_pos_739_);
lean_dec(v___x_734_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_755_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_pos_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_pos_744_ = lean_ctor_get(v_inst_730_, 0);
lean_inc_n(v_pos_744_, 2);
lean_dec_ref(v_inst_730_);
v___x_745_ = lean_apply_1(v_pos_744_, v_a_733_);
lean_inc(v_pos_739_);
v___x_746_ = lean_apply_1(v_pos_744_, v_pos_739_);
v___x_747_ = lean_apply_2(v_inst_729_, v___x_745_, v___x_746_);
v___x_748_ = lean_unbox(v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_750_; 
lean_dec_ref(v_acc_732_);
if (v_isShared_743_ == 0)
{
v___x_750_ = v___x_742_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_pos_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_err_740_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v___x_753_; 
lean_dec(v_err_740_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 0);
lean_ctor_set(v___x_742_, 1, v_acc_732_);
v___x_753_ = v___x_742_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_pos_739_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_acc_732_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b9_757_, lean_object* v_elem_758_, lean_object* v_idx_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_p_763_, lean_object* v_acc_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_760_, v_inst_762_, v_p_763_, v_acc_764_, v_a_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___boxed(lean_object* v_00_u03b1_767_, lean_object* v_00_u03b9_768_, lean_object* v_elem_769_, lean_object* v_idx_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_p_774_, lean_object* v_acc_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_Internal_Parsec_manyCore(v_00_u03b1_767_, v_00_u03b9_768_, v_elem_769_, v_idx_770_, v_inst_771_, v_inst_772_, v_inst_773_, v_p_774_, v_acc_775_, v_a_776_);
lean_dec_ref(v_inst_772_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___redArg(lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_p_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Std_Internal_Parsec_many___redArg___closed__0));
v___x_785_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_780_, v_inst_781_, v_p_782_, v___x_784_, v_a_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b9_787_, lean_object* v_elem_788_, lean_object* v_idx_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_p_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Std_Internal_Parsec_many___redArg___closed__0));
v___x_796_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_790_, v_inst_792_, v_p_793_, v___x_795_, v_a_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___boxed(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b9_798_, lean_object* v_elem_799_, lean_object* v_idx_800_, lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_p_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_Internal_Parsec_many(v_00_u03b1_797_, v_00_u03b9_798_, v_elem_799_, v_idx_800_, v_inst_801_, v_inst_802_, v_inst_803_, v_p_804_, v_a_805_);
lean_dec_ref(v_inst_802_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___redArg(lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_p_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_811_; 
lean_inc_ref(v_p_809_);
v___x_811_ = lean_apply_1(v_p_809_, v_a_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_pos_812_; lean_object* v_res_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_pos_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_pos_812_);
v_res_813_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_res_813_);
lean_dec_ref_known(v___x_811_, 2);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_mk_empty_array_with_capacity(v___x_814_);
v___x_816_ = lean_array_push(v___x_815_, v_res_813_);
v___x_817_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_807_, v_inst_808_, v_p_809_, v___x_816_, v_pos_812_);
return v___x_817_;
}
else
{
lean_object* v_pos_818_; lean_object* v_err_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_p_809_);
lean_dec_ref(v_inst_808_);
lean_dec_ref(v_inst_807_);
v_pos_818_ = lean_ctor_get(v___x_811_, 0);
v_err_819_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_811_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_err_819_);
lean_inc(v_pos_818_);
lean_dec(v___x_811_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_pos_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_err_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1(lean_object* v_00_u03b1_827_, lean_object* v_00_u03b9_828_, lean_object* v_elem_829_, lean_object* v_idx_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_p_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_836_; 
lean_inc_ref(v_p_834_);
v___x_836_ = lean_apply_1(v_p_834_, v_a_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_pos_837_; lean_object* v_res_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_pos_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_pos_837_);
v_res_838_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_res_838_);
lean_dec_ref_known(v___x_836_, 2);
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = lean_mk_empty_array_with_capacity(v___x_839_);
v___x_841_ = lean_array_push(v___x_840_, v_res_838_);
v___x_842_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_831_, v_inst_833_, v_p_834_, v___x_841_, v_pos_837_);
return v___x_842_;
}
else
{
lean_object* v_pos_843_; lean_object* v_err_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v_p_834_);
lean_dec_ref(v_inst_833_);
lean_dec_ref(v_inst_831_);
v_pos_843_ = lean_ctor_get(v___x_836_, 0);
v_err_844_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_836_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_err_844_);
lean_inc(v_pos_843_);
lean_dec(v___x_836_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_pos_843_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_err_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___boxed(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b9_853_, lean_object* v_elem_854_, lean_object* v_idx_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_p_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_Internal_Parsec_many1(v_00_u03b1_852_, v_00_u03b9_853_, v_elem_854_, v_idx_855_, v_inst_856_, v_inst_857_, v_inst_858_, v_p_859_, v_a_860_);
lean_dec_ref(v_inst_857_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___redArg(lean_object* v_inst_862_, lean_object* v_it_863_){
_start:
{
lean_object* v_hasNext_864_; lean_object* v_next_x27_865_; lean_object* v_curr_x27_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_hasNext_864_ = lean_ctor_get(v_inst_862_, 3);
lean_inc_ref(v_hasNext_864_);
v_next_x27_865_ = lean_ctor_get(v_inst_862_, 4);
lean_inc(v_next_x27_865_);
v_curr_x27_866_ = lean_ctor_get(v_inst_862_, 5);
lean_inc(v_curr_x27_866_);
lean_dec_ref(v_inst_862_);
lean_inc(v_it_863_);
v___x_867_ = lean_apply_1(v_hasNext_864_, v_it_863_);
v___x_868_ = lean_unbox(v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v_curr_x27_866_);
lean_dec(v_next_x27_865_);
v___x_869_ = lean_box(0);
v___x_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_870_, 0, v_it_863_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
return v___x_870_;
}
else
{
lean_object* v_c_871_; lean_object* v_it_x27_872_; lean_object* v___x_873_; 
lean_inc(v_it_863_);
v_c_871_ = lean_apply_2(v_curr_x27_866_, v_it_863_, lean_box(0));
v_it_x27_872_ = lean_apply_2(v_next_x27_865_, v_it_863_, lean_box(0));
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_it_x27_872_);
lean_ctor_set(v___x_873_, 1, v_c_871_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any(lean_object* v_00_u03b9_874_, lean_object* v_elem_875_, lean_object* v_idx_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_it_880_){
_start:
{
lean_object* v_hasNext_881_; lean_object* v_next_x27_882_; lean_object* v_curr_x27_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_hasNext_881_ = lean_ctor_get(v_inst_879_, 3);
lean_inc_ref(v_hasNext_881_);
v_next_x27_882_ = lean_ctor_get(v_inst_879_, 4);
lean_inc(v_next_x27_882_);
v_curr_x27_883_ = lean_ctor_get(v_inst_879_, 5);
lean_inc(v_curr_x27_883_);
lean_dec_ref(v_inst_879_);
lean_inc(v_it_880_);
v___x_884_ = lean_apply_1(v_hasNext_881_, v_it_880_);
v___x_885_ = lean_unbox(v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec(v_curr_x27_883_);
lean_dec(v_next_x27_882_);
v___x_886_ = lean_box(0);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v_it_880_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
return v___x_887_;
}
else
{
lean_object* v_c_888_; lean_object* v_it_x27_889_; lean_object* v___x_890_; 
lean_inc(v_it_880_);
v_c_888_ = lean_apply_2(v_curr_x27_883_, v_it_880_, lean_box(0));
v_it_x27_889_ = lean_apply_2(v_next_x27_882_, v_it_880_, lean_box(0));
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_it_x27_889_);
lean_ctor_set(v___x_890_, 1, v_c_888_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___boxed(lean_object* v_00_u03b9_891_, lean_object* v_elem_892_, lean_object* v_idx_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_it_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Std_Internal_Parsec_any(v_00_u03b9_891_, v_elem_892_, v_idx_893_, v_inst_894_, v_inst_895_, v_inst_896_, v_it_897_);
lean_dec_ref(v_inst_895_);
lean_dec_ref(v_inst_894_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___redArg(lean_object* v_inst_902_, lean_object* v_p_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_hasNext_905_; lean_object* v_next_x27_906_; lean_object* v_curr_x27_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_hasNext_905_ = lean_ctor_get(v_inst_902_, 3);
lean_inc_ref(v_hasNext_905_);
v_next_x27_906_ = lean_ctor_get(v_inst_902_, 4);
lean_inc(v_next_x27_906_);
v_curr_x27_907_ = lean_ctor_get(v_inst_902_, 5);
lean_inc(v_curr_x27_907_);
lean_dec_ref(v_inst_902_);
lean_inc(v_a_904_);
v___x_908_ = lean_apply_1(v_hasNext_905_, v_a_904_);
v___x_909_ = lean_unbox(v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec(v_curr_x27_907_);
lean_dec(v_next_x27_906_);
lean_dec_ref(v_p_903_);
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_911_, 0, v_a_904_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
return v___x_911_;
}
else
{
lean_object* v_c_912_; lean_object* v_it_x27_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
lean_inc_n(v_a_904_, 2);
v_c_912_ = lean_apply_2(v_curr_x27_907_, v_a_904_, lean_box(0));
v_it_x27_913_ = lean_apply_2(v_next_x27_906_, v_a_904_, lean_box(0));
lean_inc(v_c_912_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_it_x27_913_);
lean_ctor_set(v___x_914_, 1, v_c_912_);
v___x_915_ = lean_apply_1(v_p_903_, v_c_912_);
v___x_916_ = lean_unbox(v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref_known(v___x_914_, 2);
v___x_917_ = ((lean_object*)(l_Std_Internal_Parsec_satisfy___redArg___closed__1));
v___x_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_918_, 0, v_a_904_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
return v___x_918_;
}
else
{
lean_dec(v_a_904_);
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy(lean_object* v_00_u03b9_919_, lean_object* v_elem_920_, lean_object* v_idx_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_p_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_hasNext_927_; lean_object* v_next_x27_928_; lean_object* v_curr_x27_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_hasNext_927_ = lean_ctor_get(v_inst_924_, 3);
lean_inc_ref(v_hasNext_927_);
v_next_x27_928_ = lean_ctor_get(v_inst_924_, 4);
lean_inc(v_next_x27_928_);
v_curr_x27_929_ = lean_ctor_get(v_inst_924_, 5);
lean_inc(v_curr_x27_929_);
lean_dec_ref(v_inst_924_);
lean_inc(v_a_926_);
v___x_930_ = lean_apply_1(v_hasNext_927_, v_a_926_);
v___x_931_ = lean_unbox(v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_curr_x27_929_);
lean_dec(v_next_x27_928_);
lean_dec_ref(v_p_925_);
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_933_, 0, v_a_926_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
return v___x_933_;
}
else
{
lean_object* v_c_934_; lean_object* v_it_x27_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
lean_inc_n(v_a_926_, 2);
v_c_934_ = lean_apply_2(v_curr_x27_929_, v_a_926_, lean_box(0));
v_it_x27_935_ = lean_apply_2(v_next_x27_928_, v_a_926_, lean_box(0));
lean_inc(v_c_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_it_x27_935_);
lean_ctor_set(v___x_936_, 1, v_c_934_);
v___x_937_ = lean_apply_1(v_p_925_, v_c_934_);
v___x_938_ = lean_unbox(v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec_ref_known(v___x_936_, 2);
v___x_939_ = ((lean_object*)(l_Std_Internal_Parsec_satisfy___redArg___closed__1));
v___x_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_940_, 0, v_a_926_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
return v___x_940_;
}
else
{
lean_dec(v_a_926_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___boxed(lean_object* v_00_u03b9_941_, lean_object* v_elem_942_, lean_object* v_idx_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_p_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_Internal_Parsec_satisfy(v_00_u03b9_941_, v_elem_942_, v_idx_943_, v_inst_944_, v_inst_945_, v_inst_946_, v_p_947_, v_a_948_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy___redArg(lean_object* v_p_950_, lean_object* v_it_951_){
_start:
{
lean_object* v___x_952_; 
lean_inc(v_it_951_);
v___x_952_ = lean_apply_1(v_p_950_, v_it_951_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; lean_object* v_unused_962_; 
v_unused_961_ = lean_ctor_get(v___x_952_, 1);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v___x_952_, 0);
lean_dec(v_unused_962_);
v___x_954_ = v___x_952_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_dec(v___x_952_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1));
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 1);
lean_ctor_set(v___x_954_, 1, v___x_956_);
lean_ctor_set(v___x_954_, 0, v_it_951_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_it_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
else
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; lean_object* v_unused_972_; 
v_unused_971_ = lean_ctor_get(v___x_952_, 1);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v___x_952_, 0);
lean_dec(v_unused_972_);
v___x_964_ = v___x_952_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_dec(v___x_952_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 0);
lean_ctor_set(v___x_964_, 1, v___x_966_);
lean_ctor_set(v___x_964_, 0, v_it_951_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_it_951_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy(lean_object* v_00_u03b1_973_, lean_object* v_00_u03b9_974_, lean_object* v_p_975_, lean_object* v_it_976_){
_start:
{
lean_object* v___x_977_; 
lean_inc(v_it_976_);
v___x_977_ = lean_apply_1(v_p_975_, v_it_976_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_985_; 
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_986_ = lean_ctor_get(v___x_977_, 1);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_987_);
v___x_979_ = v___x_977_;
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
else
{
lean_dec(v___x_977_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1));
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 1);
lean_ctor_set(v___x_979_, 1, v___x_981_);
lean_ctor_set(v___x_979_, 0, v_it_976_);
v___x_983_ = v___x_979_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_it_976_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; 
v_unused_996_ = lean_ctor_get(v___x_977_, 1);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_997_);
v___x_989_ = v___x_977_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_dec(v___x_977_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 0);
lean_ctor_set(v___x_989_, 1, v___x_991_);
lean_ctor_set(v___x_989_, 0, v_it_976_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_it_976_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___redArg(lean_object* v_inst_998_, lean_object* v_it_999_){
_start:
{
lean_object* v_hasNext_1000_; lean_object* v_curr_x27_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_hasNext_1000_ = lean_ctor_get(v_inst_998_, 3);
lean_inc_ref(v_hasNext_1000_);
v_curr_x27_1001_ = lean_ctor_get(v_inst_998_, 5);
lean_inc(v_curr_x27_1001_);
lean_dec_ref(v_inst_998_);
lean_inc(v_it_999_);
v___x_1002_ = lean_apply_1(v_hasNext_1000_, v_it_999_);
v___x_1003_ = lean_unbox(v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v_curr_x27_1001_);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_it_999_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_inc(v_it_999_);
v___x_1006_ = lean_apply_2(v_curr_x27_1001_, v_it_999_, lean_box(0));
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_it_999_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f(lean_object* v_00_u03b9_1009_, lean_object* v_elem_1010_, lean_object* v_idx_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_inst_1014_, lean_object* v_it_1015_){
_start:
{
lean_object* v_hasNext_1016_; lean_object* v_curr_x27_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v_hasNext_1016_ = lean_ctor_get(v_inst_1014_, 3);
lean_inc_ref(v_hasNext_1016_);
v_curr_x27_1017_ = lean_ctor_get(v_inst_1014_, 5);
lean_inc(v_curr_x27_1017_);
lean_dec_ref(v_inst_1014_);
lean_inc(v_it_1015_);
v___x_1018_ = lean_apply_1(v_hasNext_1016_, v_it_1015_);
v___x_1019_ = lean_unbox(v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec(v_curr_x27_1017_);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_it_1015_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_inc(v_it_1015_);
v___x_1022_ = lean_apply_2(v_curr_x27_1017_, v_it_1015_, lean_box(0));
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_it_1015_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___boxed(lean_object* v_00_u03b9_1025_, lean_object* v_elem_1026_, lean_object* v_idx_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_it_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_Internal_Parsec_peek_x3f(v_00_u03b9_1025_, v_elem_1026_, v_idx_1027_, v_inst_1028_, v_inst_1029_, v_inst_1030_, v_it_1031_);
lean_dec_ref(v_inst_1029_);
lean_dec_ref(v_inst_1028_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___redArg(lean_object* v_inst_1033_, lean_object* v_p_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_hasNext_1036_; lean_object* v_curr_x27_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_hasNext_1036_ = lean_ctor_get(v_inst_1033_, 3);
lean_inc_ref(v_hasNext_1036_);
v_curr_x27_1037_ = lean_ctor_get(v_inst_1033_, 5);
lean_inc(v_curr_x27_1037_);
lean_dec_ref(v_inst_1033_);
lean_inc(v_a_1035_);
v___x_1038_ = lean_apply_1(v_hasNext_1036_, v_a_1035_);
v___x_1039_ = lean_unbox(v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec(v_curr_x27_1037_);
lean_dec_ref(v_p_1034_);
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_a_1035_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
lean_inc(v_a_1035_);
v___x_1042_ = lean_apply_2(v_curr_x27_1037_, v_a_1035_, lean_box(0));
lean_inc(v___x_1042_);
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
v___x_1044_ = lean_apply_1(v_p_1034_, v___x_1042_);
v___x_1045_ = lean_unbox(v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref_known(v___x_1043_, 1);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_a_1035_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1035_);
lean_ctor_set(v___x_1048_, 1, v___x_1043_);
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f(lean_object* v_00_u03b9_1049_, lean_object* v_elem_1050_, lean_object* v_idx_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_p_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_hasNext_1057_; lean_object* v_curr_x27_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_hasNext_1057_ = lean_ctor_get(v_inst_1054_, 3);
lean_inc_ref(v_hasNext_1057_);
v_curr_x27_1058_ = lean_ctor_get(v_inst_1054_, 5);
lean_inc(v_curr_x27_1058_);
lean_dec_ref(v_inst_1054_);
lean_inc(v_a_1056_);
v___x_1059_ = lean_apply_1(v_hasNext_1057_, v_a_1056_);
v___x_1060_ = lean_unbox(v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec(v_curr_x27_1058_);
lean_dec_ref(v_p_1055_);
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_a_1056_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
lean_inc(v_a_1056_);
v___x_1063_ = lean_apply_2(v_curr_x27_1058_, v_a_1056_, lean_box(0));
lean_inc(v___x_1063_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
v___x_1065_ = lean_apply_1(v_p_1055_, v___x_1063_);
v___x_1066_ = lean_unbox(v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref_known(v___x_1064_, 1);
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_a_1056_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_a_1056_);
lean_ctor_set(v___x_1069_, 1, v___x_1064_);
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___boxed(lean_object* v_00_u03b9_1070_, lean_object* v_elem_1071_, lean_object* v_idx_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v_p_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Std_Internal_Parsec_peekWhen_x3f(v_00_u03b9_1070_, v_elem_1071_, v_idx_1072_, v_inst_1073_, v_inst_1074_, v_inst_1075_, v_p_1076_, v_a_1077_);
lean_dec_ref(v_inst_1074_);
lean_dec_ref(v_inst_1073_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___redArg(lean_object* v_inst_1079_, lean_object* v_it_1080_){
_start:
{
lean_object* v_hasNext_1081_; lean_object* v_curr_x27_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v_hasNext_1081_ = lean_ctor_get(v_inst_1079_, 3);
lean_inc_ref(v_hasNext_1081_);
v_curr_x27_1082_ = lean_ctor_get(v_inst_1079_, 5);
lean_inc(v_curr_x27_1082_);
lean_dec_ref(v_inst_1079_);
lean_inc(v_it_1080_);
v___x_1083_ = lean_apply_1(v_hasNext_1081_, v_it_1080_);
v___x_1084_ = lean_unbox(v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec(v_curr_x27_1082_);
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_it_1080_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_inc(v_it_1080_);
v___x_1087_ = lean_apply_2(v_curr_x27_1082_, v_it_1080_, lean_box(0));
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_it_1080_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21(lean_object* v_00_u03b9_1089_, lean_object* v_elem_1090_, lean_object* v_idx_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_it_1095_){
_start:
{
lean_object* v_hasNext_1096_; lean_object* v_curr_x27_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_hasNext_1096_ = lean_ctor_get(v_inst_1094_, 3);
lean_inc_ref(v_hasNext_1096_);
v_curr_x27_1097_ = lean_ctor_get(v_inst_1094_, 5);
lean_inc(v_curr_x27_1097_);
lean_dec_ref(v_inst_1094_);
lean_inc(v_it_1095_);
v___x_1098_ = lean_apply_1(v_hasNext_1096_, v_it_1095_);
v___x_1099_ = lean_unbox(v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_curr_x27_1097_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_it_1095_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_inc(v_it_1095_);
v___x_1102_ = lean_apply_2(v_curr_x27_1097_, v_it_1095_, lean_box(0));
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_it_1095_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___boxed(lean_object* v_00_u03b9_1104_, lean_object* v_elem_1105_, lean_object* v_idx_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_it_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_Internal_Parsec_peek_x21(v_00_u03b9_1104_, v_elem_1105_, v_idx_1106_, v_inst_1107_, v_inst_1108_, v_inst_1109_, v_it_1110_);
lean_dec_ref(v_inst_1108_);
lean_dec_ref(v_inst_1107_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___redArg(lean_object* v_inst_1112_, lean_object* v_default_1113_, lean_object* v_it_1114_){
_start:
{
lean_object* v_hasNext_1115_; lean_object* v_curr_x27_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_hasNext_1115_ = lean_ctor_get(v_inst_1112_, 3);
lean_inc_ref(v_hasNext_1115_);
v_curr_x27_1116_ = lean_ctor_get(v_inst_1112_, 5);
lean_inc(v_curr_x27_1116_);
lean_dec_ref(v_inst_1112_);
lean_inc(v_it_1114_);
v___x_1117_ = lean_apply_1(v_hasNext_1115_, v_it_1114_);
v___x_1118_ = lean_unbox(v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec(v_curr_x27_1116_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_it_1114_);
lean_ctor_set(v___x_1119_, 1, v_default_1113_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_default_1113_);
lean_inc(v_it_1114_);
v___x_1120_ = lean_apply_2(v_curr_x27_1116_, v_it_1114_, lean_box(0));
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_it_1114_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD(lean_object* v_00_u03b9_1122_, lean_object* v_elem_1123_, lean_object* v_idx_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_default_1128_, lean_object* v_it_1129_){
_start:
{
lean_object* v_hasNext_1130_; lean_object* v_curr_x27_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_hasNext_1130_ = lean_ctor_get(v_inst_1127_, 3);
lean_inc_ref(v_hasNext_1130_);
v_curr_x27_1131_ = lean_ctor_get(v_inst_1127_, 5);
lean_inc(v_curr_x27_1131_);
lean_dec_ref(v_inst_1127_);
lean_inc(v_it_1129_);
v___x_1132_ = lean_apply_1(v_hasNext_1130_, v_it_1129_);
v___x_1133_ = lean_unbox(v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v_curr_x27_1131_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_it_1129_);
lean_ctor_set(v___x_1134_, 1, v_default_1128_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_default_1128_);
lean_inc(v_it_1129_);
v___x_1135_ = lean_apply_2(v_curr_x27_1131_, v_it_1129_, lean_box(0));
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_it_1129_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___boxed(lean_object* v_00_u03b9_1137_, lean_object* v_elem_1138_, lean_object* v_idx_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_default_1143_, lean_object* v_it_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Std_Internal_Parsec_peekD(v_00_u03b9_1137_, v_elem_1138_, v_idx_1139_, v_inst_1140_, v_inst_1141_, v_inst_1142_, v_default_1143_, v_it_1144_);
lean_dec_ref(v_inst_1141_);
lean_dec_ref(v_inst_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___redArg(lean_object* v_inst_1146_, lean_object* v_it_1147_){
_start:
{
lean_object* v_hasNext_1148_; lean_object* v_next_x27_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v_hasNext_1148_ = lean_ctor_get(v_inst_1146_, 3);
lean_inc_ref(v_hasNext_1148_);
v_next_x27_1149_ = lean_ctor_get(v_inst_1146_, 4);
lean_inc(v_next_x27_1149_);
lean_dec_ref(v_inst_1146_);
lean_inc(v_it_1147_);
v___x_1150_ = lean_apply_1(v_hasNext_1148_, v_it_1147_);
v___x_1151_ = lean_unbox(v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_next_x27_1149_);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_it_1147_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_apply_2(v_next_x27_1149_, v_it_1147_, lean_box(0));
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip(lean_object* v_00_u03b9_1157_, lean_object* v_elem_1158_, lean_object* v_idx_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_it_1163_){
_start:
{
lean_object* v_hasNext_1164_; lean_object* v_next_x27_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_hasNext_1164_ = lean_ctor_get(v_inst_1162_, 3);
lean_inc_ref(v_hasNext_1164_);
v_next_x27_1165_ = lean_ctor_get(v_inst_1162_, 4);
lean_inc(v_next_x27_1165_);
lean_dec_ref(v_inst_1162_);
lean_inc(v_it_1163_);
v___x_1166_ = lean_apply_1(v_hasNext_1164_, v_it_1163_);
v___x_1167_ = lean_unbox(v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v_next_x27_1165_);
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_it_1163_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_apply_2(v_next_x27_1165_, v_it_1163_, lean_box(0));
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___boxed(lean_object* v_00_u03b9_1173_, lean_object* v_elem_1174_, lean_object* v_idx_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_it_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Std_Internal_Parsec_skip(v_00_u03b9_1173_, v_elem_1174_, v_idx_1175_, v_inst_1176_, v_inst_1177_, v_inst_1178_, v_it_1179_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___redArg(lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_p_1183_, lean_object* v_acc_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1186_; 
lean_inc_ref(v_p_1183_);
lean_inc(v_a_1185_);
v___x_1186_ = lean_apply_1(v_p_1183_, v_a_1185_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_pos_1187_; lean_object* v_res_1188_; uint32_t v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_a_1185_);
v_pos_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_pos_1187_);
v_res_1188_ = lean_ctor_get(v___x_1186_, 1);
lean_inc(v_res_1188_);
lean_dec_ref_known(v___x_1186_, 2);
v___x_1189_ = lean_unbox_uint32(v_res_1188_);
lean_dec(v_res_1188_);
v___x_1190_ = lean_string_push(v_acc_1184_, v___x_1189_);
v_acc_1184_ = v___x_1190_;
v_a_1185_ = v_pos_1187_;
goto _start;
}
else
{
lean_object* v_pos_1192_; lean_object* v_err_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v_p_1183_);
v_pos_1192_ = lean_ctor_get(v___x_1186_, 0);
v_err_1193_ = lean_ctor_get(v___x_1186_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1195_ = v___x_1186_;
v_isShared_1196_ = v_isSharedCheck_1208_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_err_1193_);
lean_inc(v_pos_1192_);
lean_dec(v___x_1186_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1208_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_pos_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_pos_1197_ = lean_ctor_get(v_inst_1182_, 0);
lean_inc_n(v_pos_1197_, 2);
lean_dec_ref(v_inst_1182_);
v___x_1198_ = lean_apply_1(v_pos_1197_, v_a_1185_);
lean_inc(v_pos_1192_);
v___x_1199_ = lean_apply_1(v_pos_1197_, v_pos_1192_);
v___x_1200_ = lean_apply_2(v_inst_1181_, v___x_1198_, v___x_1199_);
v___x_1201_ = lean_unbox(v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1203_; 
lean_dec_ref(v_acc_1184_);
if (v_isShared_1196_ == 0)
{
v___x_1203_ = v___x_1195_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_pos_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_err_1193_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v___x_1206_; 
lean_dec(v_err_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set_tag(v___x_1195_, 0);
lean_ctor_set(v___x_1195_, 1, v_acc_1184_);
v___x_1206_ = v___x_1195_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_pos_1192_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_acc_1184_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore(lean_object* v_00_u03b9_1209_, lean_object* v_elem_1210_, lean_object* v_idx_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_p_1215_, lean_object* v_acc_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1212_, v_inst_1214_, v_p_1215_, v_acc_1216_, v_a_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___boxed(lean_object* v_00_u03b9_1219_, lean_object* v_elem_1220_, lean_object* v_idx_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_p_1225_, lean_object* v_acc_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_Internal_Parsec_manyCharsCore(v_00_u03b9_1219_, v_elem_1220_, v_idx_1221_, v_inst_1222_, v_inst_1223_, v_inst_1224_, v_p_1225_, v_acc_1226_, v_a_1227_);
lean_dec_ref(v_inst_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___redArg(lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_p_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0));
v___x_1234_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1229_, v_inst_1230_, v_p_1231_, v___x_1233_, v_a_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars(lean_object* v_00_u03b9_1235_, lean_object* v_elem_1236_, lean_object* v_idx_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_p_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0));
v___x_1244_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1238_, v_inst_1240_, v_p_1241_, v___x_1243_, v_a_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___boxed(lean_object* v_00_u03b9_1245_, lean_object* v_elem_1246_, lean_object* v_idx_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_p_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_Internal_Parsec_manyChars(v_00_u03b9_1245_, v_elem_1246_, v_idx_1247_, v_inst_1248_, v_inst_1249_, v_inst_1250_, v_p_1251_, v_a_1252_);
lean_dec_ref(v_inst_1249_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___redArg(lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_p_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1258_; 
lean_inc_ref(v_p_1256_);
v___x_1258_ = lean_apply_1(v_p_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_pos_1259_; lean_object* v_res_1260_; lean_object* v___x_1261_; uint32_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_pos_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_pos_1259_);
v_res_1260_ = lean_ctor_get(v___x_1258_, 1);
lean_inc(v_res_1260_);
lean_dec_ref_known(v___x_1258_, 2);
v___x_1261_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0));
v___x_1262_ = lean_unbox_uint32(v_res_1260_);
lean_dec(v_res_1260_);
v___x_1263_ = lean_string_push(v___x_1261_, v___x_1262_);
v___x_1264_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1254_, v_inst_1255_, v_p_1256_, v___x_1263_, v_pos_1259_);
return v___x_1264_;
}
else
{
lean_object* v_pos_1265_; lean_object* v_err_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_p_1256_);
lean_dec_ref(v_inst_1255_);
lean_dec_ref(v_inst_1254_);
v_pos_1265_ = lean_ctor_get(v___x_1258_, 0);
v_err_1266_ = lean_ctor_get(v___x_1258_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1258_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_err_1266_);
lean_inc(v_pos_1265_);
lean_dec(v___x_1258_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_pos_1265_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_err_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars(lean_object* v_00_u03b9_1274_, lean_object* v_elem_1275_, lean_object* v_idx_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_p_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1282_; 
lean_inc_ref(v_p_1280_);
v___x_1282_ = lean_apply_1(v_p_1280_, v_a_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_pos_1283_; lean_object* v_res_1284_; lean_object* v___x_1285_; uint32_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_pos_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_pos_1283_);
v_res_1284_ = lean_ctor_get(v___x_1282_, 1);
lean_inc(v_res_1284_);
lean_dec_ref_known(v___x_1282_, 2);
v___x_1285_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0));
v___x_1286_ = lean_unbox_uint32(v_res_1284_);
lean_dec(v_res_1284_);
v___x_1287_ = lean_string_push(v___x_1285_, v___x_1286_);
v___x_1288_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1277_, v_inst_1279_, v_p_1280_, v___x_1287_, v_pos_1283_);
return v___x_1288_;
}
else
{
lean_object* v_pos_1289_; lean_object* v_err_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_p_1280_);
lean_dec_ref(v_inst_1279_);
lean_dec_ref(v_inst_1277_);
v_pos_1289_ = lean_ctor_get(v___x_1282_, 0);
v_err_1290_ = lean_ctor_get(v___x_1282_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1282_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_err_1290_);
lean_inc(v_pos_1289_);
lean_dec(v___x_1282_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_pos_1289_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_err_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___boxed(lean_object* v_00_u03b9_1298_, lean_object* v_elem_1299_, lean_object* v_idx_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_p_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Std_Internal_Parsec_many1Chars(v_00_u03b9_1298_, v_elem_1299_, v_idx_1300_, v_inst_1301_, v_inst_1302_, v_inst_1303_, v_p_1304_, v_a_1305_);
lean_dec_ref(v_inst_1302_);
return v_res_1306_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
