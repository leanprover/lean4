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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Internal_Parsec_Error_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_s_7_; lean_object* v___x_8_; 
v_s_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_s_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_s_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Internal_Parsec_Error_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_eof_elim___redArg(lean_object* v_t_21_, lean_object* v_eof_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_21_, v_eof_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_eof_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_eof_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_25_, v_eof_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_other_elim___redArg(lean_object* v_t_29_, lean_object* v_other_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_29_, v_other_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_Error_other_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_other_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Internal_Parsec_Error_ctorElim___redArg(v_t_33_, v_other_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instReprError_repr___closed__2(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(2u);
v___x_41_ = lean_nat_to_int(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Std_Internal_Parsec_instReprError_repr___closed__3(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_to_int(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprError_repr(lean_object* v_x_50_, lean_object* v_prec_51_){
_start:
{
lean_object* v___y_53_; 
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(1024u);
v___x_60_ = lean_nat_dec_le(v___x_59_, v_prec_51_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
v___y_53_ = v___x_61_;
goto v___jp_52_;
}
else
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
v___y_53_ = v___x_62_;
goto v___jp_52_;
}
}
else
{
lean_object* v_s_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_83_; 
v_s_63_ = lean_ctor_get(v_x_50_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_83_ == 0)
{
v___x_65_ = v_x_50_;
v_isShared_66_ = v_isSharedCheck_83_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_s_63_);
lean_dec(v_x_50_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_83_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___y_68_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1024u);
v___x_80_ = lean_nat_dec_le(v___x_79_, v_prec_51_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
v___y_68_ = v___x_82_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_69_ = ((lean_object*)(l_Std_Internal_Parsec_instReprError_repr___closed__6));
v___x_70_ = l_String_quote(v_s_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 3);
lean_ctor_set(v___x_65_, 0, v___x_70_);
v___x_72_ = v___x_65_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_78_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_69_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
lean_inc(v___y_68_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_68_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = 0;
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = l_Repr_addAppParen(v___x_76_, v_prec_51_);
return v___x_77_;
}
}
}
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_54_ = ((lean_object*)(l_Std_Internal_Parsec_instReprError_repr___closed__1));
lean_inc(v___y_53_);
v___x_55_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_55_, 0, v___y_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = 0;
v___x_57_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*1, v___x_56_);
v___x_58_ = l_Repr_addAppParen(v___x_57_, v_prec_51_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprError_repr___boxed(lean_object* v_x_84_, lean_object* v_prec_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Internal_Parsec_instReprError_repr(v_x_84_, v_prec_85_);
lean_dec(v_prec_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instToStringError___lam__0(lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v___x_91_; 
v___x_91_ = ((lean_object*)(l_Std_Internal_Parsec_instToStringError___lam__0___closed__0));
return v___x_91_;
}
else
{
lean_object* v_s_92_; 
v_s_92_ = lean_ctor_get(v_x_90_, 0);
lean_inc_ref(v_s_92_);
return v_s_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instToStringError___lam__0___boxed(lean_object* v_x_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Internal_Parsec_instToStringError___lam__0(v_x_93_);
lean_dec(v_x_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___impl___redArg(lean_object* v_x_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_tag_nat(v_x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___impl___redArg___boxed(lean_object* v_x_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Internal_Parsec_ParseResult_ctorIdx___impl___redArg(v_x_99_);
lean_dec_ref(v_x_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___impl(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b9_102_, lean_object* v_x_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_tag_nat(v_x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorIdx___impl___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b9_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_Internal_Parsec_ParseResult_ctorIdx___impl(v_00_u03b1_105_, v_00_u03b9_106_, v_x_107_);
lean_dec_ref(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(lean_object* v_t_109_, lean_object* v_k_110_){
_start:
{
lean_object* v_pos_111_; lean_object* v_res_112_; lean_object* v___x_113_; 
v_pos_111_ = lean_ctor_get(v_t_109_, 0);
lean_inc(v_pos_111_);
v_res_112_ = lean_ctor_get(v_t_109_, 1);
lean_inc(v_res_112_);
lean_dec_ref(v_t_109_);
v___x_113_ = lean_apply_2(v_k_110_, v_pos_111_, v_res_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b9_115_, lean_object* v_motive_116_, lean_object* v_ctorIdx_117_, lean_object* v_t_118_, lean_object* v_h_119_, lean_object* v_k_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_118_, v_k_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_ctorElim___boxed(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b9_123_, lean_object* v_motive_124_, lean_object* v_ctorIdx_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_k_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_Internal_Parsec_ParseResult_ctorElim(v_00_u03b1_122_, v_00_u03b9_123_, v_motive_124_, v_ctorIdx_125_, v_t_126_, v_h_127_, v_k_128_);
lean_dec(v_ctorIdx_125_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_success_elim___redArg(lean_object* v_t_130_, lean_object* v_success_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_130_, v_success_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_success_elim(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b9_134_, lean_object* v_motive_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_success_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_136_, v_success_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_error_elim___redArg(lean_object* v_t_140_, lean_object* v_error_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_140_, v_error_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_ParseResult_error_elim(lean_object* v_00_u03b1_143_, lean_object* v_00_u03b9_144_, lean_object* v_motive_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_error_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_Internal_Parsec_ParseResult_ctorElim___redArg(v_t_146_, v_error_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg(lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_x_164_, lean_object* v_prec_165_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v_pos_166_; lean_object* v_res_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_191_; 
v_pos_166_ = lean_ctor_get(v_x_164_, 0);
v_res_167_ = lean_ctor_get(v_x_164_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_191_ == 0)
{
v___x_169_ = v_x_164_;
v_isShared_170_ = v_isSharedCheck_191_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_res_167_);
lean_inc(v_pos_166_);
lean_dec(v_x_164_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_191_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___y_172_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1024u);
v___x_188_ = lean_nat_dec_le(v___x_187_, v_prec_165_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
v___y_172_ = v___x_189_;
goto v___jp_171_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
v___y_172_ = v___x_190_;
goto v___jp_171_;
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_173_ = lean_box(1);
v___x_174_ = ((lean_object*)(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__2));
v___x_175_ = lean_unsigned_to_nat(1024u);
v___x_176_ = lean_apply_2(v_inst_163_, v_pos_166_, v___x_175_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 5);
lean_ctor_set(v___x_169_, 1, v___x_176_);
lean_ctor_set(v___x_169_, 0, v___x_174_);
v___x_178_ = v___x_169_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_176_);
v___x_178_ = v_reuseFailAlloc_186_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_173_);
v___x_180_ = lean_apply_2(v_inst_162_, v_res_167_, v___x_175_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
lean_inc(v___y_172_);
v___x_182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_182_, 0, v___y_172_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = 0;
v___x_184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*1, v___x_183_);
v___x_185_ = l_Repr_addAppParen(v___x_184_, v_prec_165_);
return v___x_185_;
}
}
}
}
else
{
lean_object* v_pos_192_; lean_object* v_err_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_217_; 
lean_dec_ref(v_inst_162_);
v_pos_192_ = lean_ctor_get(v_x_164_, 0);
v_err_193_ = lean_ctor_get(v_x_164_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_217_ == 0)
{
v___x_195_ = v_x_164_;
v_isShared_196_ = v_isSharedCheck_217_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_err_193_);
lean_inc(v_pos_192_);
lean_dec(v_x_164_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_217_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___y_198_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(1024u);
v___x_214_ = lean_nat_dec_le(v___x_213_, v_prec_165_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__2, &l_Std_Internal_Parsec_instReprError_repr___closed__2_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__2);
v___y_198_ = v___x_215_;
goto v___jp_197_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Std_Internal_Parsec_instReprError_repr___closed__3, &l_Std_Internal_Parsec_instReprError_repr___closed__3_once, _init_l_Std_Internal_Parsec_instReprError_repr___closed__3);
v___y_198_ = v___x_216_;
goto v___jp_197_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_199_ = lean_box(1);
v___x_200_ = ((lean_object*)(l_Std_Internal_Parsec_instReprParseResult_repr___redArg___closed__5));
v___x_201_ = lean_unsigned_to_nat(1024u);
v___x_202_ = lean_apply_2(v_inst_163_, v_pos_192_, v___x_201_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 5);
lean_ctor_set(v___x_195_, 1, v___x_202_);
lean_ctor_set(v___x_195_, 0, v___x_200_);
v___x_204_ = v___x_195_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_212_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_199_);
v___x_206_ = l_Std_Internal_Parsec_instReprError_repr(v_err_193_, v___x_201_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_inc(v___y_198_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_198_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_165_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___redArg___boxed(lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_x_220_, lean_object* v_prec_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(v_inst_218_, v_inst_219_, v_x_220_, v_prec_221_);
lean_dec(v_prec_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr(lean_object* v_00_u03b1_223_, lean_object* v_00_u03b9_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_x_227_, lean_object* v_prec_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_Internal_Parsec_instReprParseResult_repr___redArg(v_inst_225_, v_inst_226_, v_x_227_, v_prec_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult_repr___boxed(lean_object* v_00_u03b1_230_, lean_object* v_00_u03b9_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_x_234_, lean_object* v_prec_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Internal_Parsec_instReprParseResult_repr(v_00_u03b1_230_, v_00_u03b9_231_, v_inst_232_, v_inst_233_, v_x_234_, v_prec_235_);
lean_dec(v_prec_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult___redArg(lean_object* v_inst_237_, lean_object* v_inst_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instReprParseResult_repr___boxed), 6, 4);
lean_closure_set(v___x_239_, 0, lean_box(0));
lean_closure_set(v___x_239_, 1, lean_box(0));
lean_closure_set(v___x_239_, 2, v_inst_237_);
lean_closure_set(v___x_239_, 3, v_inst_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instReprParseResult(lean_object* v_00_u03b1_240_, lean_object* v_00_u03b9_241_, lean_object* v_inst_242_, lean_object* v_inst_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instReprParseResult_repr___boxed), 6, 4);
lean_closure_set(v___x_244_, 0, lean_box(0));
lean_closure_set(v___x_244_, 1, lean_box(0));
lean_closure_set(v___x_244_, 2, v_inst_242_);
lean_closure_set(v___x_244_, 3, v_inst_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg___lam__0(lean_object* v_it_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1));
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v_it_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg(){
_start:
{
lean_object* v___f_253_; 
v___f_253_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___closed__0));
return v___f_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited___redArg___boxed(lean_object* v___dummy_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Internal_Parsec_instInhabited___redArg();
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instInhabited(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b9_257_){
_start:
{
lean_object* v___f_258_; 
v___f_258_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___closed__0));
return v___f_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure___redArg(lean_object* v_a_259_, lean_object* v_it_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_it_260_);
lean_ctor_set(v___x_261_, 1, v_a_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_pure(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b9_263_, lean_object* v_a_264_, lean_object* v_it_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_it_265_);
lean_ctor_set(v___x_266_, 1, v_a_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind___redArg(lean_object* v_f_267_, lean_object* v_g_268_, lean_object* v_it_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_apply_1(v_f_267_, v_it_269_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_pos_271_; lean_object* v_res_272_; lean_object* v___x_273_; 
v_pos_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_pos_271_);
v_res_272_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_res_272_);
lean_dec_ref_known(v___x_270_, 2);
v___x_273_ = lean_apply_2(v_g_268_, v_res_272_, v_pos_271_);
return v___x_273_;
}
else
{
lean_object* v_pos_274_; lean_object* v_err_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_g_268_);
v_pos_274_ = lean_ctor_get(v___x_270_, 0);
v_err_275_ = lean_ctor_get(v___x_270_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_270_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_err_275_);
lean_inc(v_pos_274_);
lean_dec(v___x_270_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_pos_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_err_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_bind(lean_object* v_00_u03b9_283_, lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_f_286_, lean_object* v_g_287_, lean_object* v_it_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_apply_1(v_f_286_, v_it_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_pos_290_; lean_object* v_res_291_; lean_object* v___x_292_; 
v_pos_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_pos_290_);
v_res_291_ = lean_ctor_get(v___x_289_, 1);
lean_inc(v_res_291_);
lean_dec_ref_known(v___x_289_, 2);
v___x_292_ = lean_apply_2(v_g_287_, v_res_291_, v_pos_290_);
return v___x_292_;
}
else
{
lean_object* v_pos_293_; lean_object* v_err_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_g_287_);
v_pos_293_ = lean_ctor_get(v___x_289_, 0);
v_err_294_ = lean_ctor_get(v___x_289_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_289_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_err_294_);
lean_inc(v_pos_293_);
lean_dec(v___x_289_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_pos_293_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_err_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail___redArg(lean_object* v_msg_302_, lean_object* v_it_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_msg_302_);
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v_it_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_fail(lean_object* v_00_u03b1_306_, lean_object* v_00_u03b9_307_, lean_object* v_msg_308_, lean_object* v_it_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_msg_308_);
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v_it_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___redArg(lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_p_314_, lean_object* v_csuccess_315_, lean_object* v_cerror_316_, lean_object* v_it_317_){
_start:
{
lean_object* v___x_318_; 
lean_inc(v_it_317_);
v___x_318_ = lean_apply_1(v_p_314_, v_it_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_pos_319_; lean_object* v_res_320_; lean_object* v___x_321_; 
lean_dec(v_it_317_);
lean_dec_ref(v_cerror_316_);
lean_dec_ref(v_inst_313_);
lean_dec_ref(v_inst_312_);
v_pos_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_pos_319_);
v_res_320_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_res_320_);
lean_dec_ref_known(v___x_318_, 2);
v___x_321_ = lean_apply_2(v_csuccess_315_, v_res_320_, v_pos_319_);
return v___x_321_;
}
else
{
lean_object* v_pos_322_; lean_object* v_err_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_csuccess_315_);
v_pos_322_ = lean_ctor_get(v___x_318_, 0);
v_err_323_ = lean_ctor_get(v___x_318_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_337_ == 0)
{
v___x_325_ = v___x_318_;
v_isShared_326_ = v_isSharedCheck_337_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_err_323_);
lean_inc(v_pos_322_);
lean_dec(v___x_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_337_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_pos_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_pos_327_ = lean_ctor_get(v_inst_313_, 0);
lean_inc_n(v_pos_327_, 2);
lean_dec_ref(v_inst_313_);
v___x_328_ = lean_apply_1(v_pos_327_, v_it_317_);
lean_inc(v_pos_322_);
v___x_329_ = lean_apply_1(v_pos_327_, v_pos_322_);
v___x_330_ = lean_apply_2(v_inst_312_, v___x_328_, v___x_329_);
v___x_331_ = lean_unbox(v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v_cerror_316_);
if (v_isShared_326_ == 0)
{
v___x_333_ = v___x_325_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_pos_322_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_err_323_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_del_object(v___x_325_);
lean_dec(v_err_323_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_apply_2(v_cerror_316_, v___x_335_, v_pos_322_);
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch(lean_object* v_00_u03b1_338_, lean_object* v_00_u03b9_339_, lean_object* v_elem_340_, lean_object* v_idx_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_00_u03b2_345_, lean_object* v_p_346_, lean_object* v_csuccess_347_, lean_object* v_cerror_348_, lean_object* v_it_349_){
_start:
{
lean_object* v___x_350_; 
lean_inc(v_it_349_);
v___x_350_ = lean_apply_1(v_p_346_, v_it_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_pos_351_; lean_object* v_res_352_; lean_object* v___x_353_; 
lean_dec(v_it_349_);
lean_dec_ref(v_cerror_348_);
lean_dec_ref(v_inst_344_);
lean_dec_ref(v_inst_342_);
v_pos_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_pos_351_);
v_res_352_ = lean_ctor_get(v___x_350_, 1);
lean_inc(v_res_352_);
lean_dec_ref_known(v___x_350_, 2);
v___x_353_ = lean_apply_2(v_csuccess_347_, v_res_352_, v_pos_351_);
return v___x_353_;
}
else
{
lean_object* v_pos_354_; lean_object* v_err_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v_csuccess_347_);
v_pos_354_ = lean_ctor_get(v___x_350_, 0);
v_err_355_ = lean_ctor_get(v___x_350_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_369_ == 0)
{
v___x_357_ = v___x_350_;
v_isShared_358_ = v_isSharedCheck_369_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_err_355_);
lean_inc(v_pos_354_);
lean_dec(v___x_350_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_369_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_pos_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_pos_359_ = lean_ctor_get(v_inst_344_, 0);
lean_inc_n(v_pos_359_, 2);
lean_dec_ref(v_inst_344_);
v___x_360_ = lean_apply_1(v_pos_359_, v_it_349_);
lean_inc(v_pos_354_);
v___x_361_ = lean_apply_1(v_pos_359_, v_pos_354_);
v___x_362_ = lean_apply_2(v_inst_342_, v___x_360_, v___x_361_);
v___x_363_ = lean_unbox(v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_365_; 
lean_dec_ref(v_cerror_348_);
if (v_isShared_358_ == 0)
{
v___x_365_ = v___x_357_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_pos_354_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_err_355_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_del_object(v___x_357_);
lean_dec(v_err_355_);
v___x_367_ = lean_box(0);
v___x_368_ = lean_apply_2(v_cerror_348_, v___x_367_, v_pos_354_);
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_tryCatch___boxed(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b9_371_, lean_object* v_elem_372_, lean_object* v_idx_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_00_u03b2_377_, lean_object* v_p_378_, lean_object* v_csuccess_379_, lean_object* v_cerror_380_, lean_object* v_it_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Internal_Parsec_tryCatch(v_00_u03b1_370_, v_00_u03b9_371_, v_elem_372_, v_idx_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_00_u03b2_377_, v_p_378_, v_csuccess_379_, v_cerror_380_, v_it_381_);
lean_dec_ref(v_inst_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__0(lean_object* v_00_u03b1_383_, lean_object* v_00_u03b2_384_, lean_object* v_f_385_, lean_object* v_x_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_apply_1(v_x_386_, v___y_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_pos_389_; lean_object* v_res_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v_pos_389_ = lean_ctor_get(v___x_388_, 0);
v_res_390_ = lean_ctor_get(v___x_388_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_398_ == 0)
{
v___x_392_ = v___x_388_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_res_390_);
lean_inc(v_pos_389_);
lean_dec(v___x_388_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_apply_1(v_f_385_, v_res_390_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_394_);
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_pos_389_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_pos_399_; lean_object* v_err_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_f_385_);
v_pos_399_ = lean_ctor_get(v___x_388_, 0);
v_err_400_ = lean_ctor_get(v___x_388_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_388_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_err_400_);
lean_inc(v_pos_399_);
lean_dec(v___x_388_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_pos_399_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_err_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__1(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_apply_1(v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_pos_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_pos_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_413_, 1);
lean_dec(v_unused_422_);
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_pos_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___y_410_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_pos_414_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___y_410_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v_pos_423_; lean_object* v_err_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v___y_410_);
v_pos_423_ = lean_ctor_get(v___x_413_, 0);
v_err_424_ = lean_ctor_get(v___x_413_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_413_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_err_424_);
lean_inc(v_pos_423_);
lean_dec(v___x_413_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_pos_423_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_err_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__2(lean_object* v_00_u03b1_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___y_434_);
lean_ctor_set(v___x_435_, 1, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__3(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_f_438_, lean_object* v_x_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_apply_1(v_f_438_, v___y_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_pos_442_; lean_object* v_res_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_pos_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_pos_442_);
v_res_443_ = lean_ctor_get(v___x_441_, 1);
lean_inc(v_res_443_);
lean_dec_ref_known(v___x_441_, 2);
v___x_444_ = lean_box(0);
v___x_445_ = lean_apply_2(v_x_439_, v___x_444_, v_pos_442_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_pos_446_; lean_object* v_res_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_pos_446_ = lean_ctor_get(v___x_445_, 0);
v_res_447_ = lean_ctor_get(v___x_445_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_res_447_);
lean_inc(v_pos_446_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_apply_1(v_res_443_, v_res_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_pos_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_pos_456_; lean_object* v_err_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_res_443_);
v_pos_456_ = lean_ctor_get(v___x_445_, 0);
v_err_457_ = lean_ctor_get(v___x_445_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_445_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_err_457_);
lean_inc(v_pos_456_);
lean_dec(v___x_445_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_pos_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_err_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_pos_465_; lean_object* v_err_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec_ref(v_x_439_);
v_pos_465_ = lean_ctor_get(v___x_441_, 0);
v_err_466_ = lean_ctor_get(v___x_441_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_441_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_err_466_);
lean_inc(v_pos_465_);
lean_dec(v___x_441_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_pos_465_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_err_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__4(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_x_476_, lean_object* v_y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = lean_apply_1(v_x_476_, v___y_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_pos_480_; lean_object* v_res_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_pos_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_pos_480_);
v_res_481_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_res_481_);
lean_dec_ref_known(v___x_479_, 2);
v___x_482_ = lean_box(0);
v___x_483_ = lean_apply_2(v_y_477_, v___x_482_, v_pos_480_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_pos_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_pos_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; 
v_unused_492_ = lean_ctor_get(v___x_483_, 1);
lean_dec(v_unused_492_);
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_pos_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_res_481_);
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_pos_484_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_res_481_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_object* v_pos_493_; lean_object* v_err_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_res_481_);
v_pos_493_ = lean_ctor_get(v___x_483_, 0);
v_err_494_ = lean_ctor_get(v___x_483_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_483_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_err_494_);
lean_inc(v_pos_493_);
lean_dec(v___x_483_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_pos_493_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_err_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_dec_ref(v_y_477_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___lam__5(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_x_504_, lean_object* v_y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_apply_1(v_x_504_, v___y_506_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_pos_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_pos_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_pos_508_);
lean_dec_ref_known(v___x_507_, 2);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_2(v_y_505_, v___x_509_, v_pos_508_);
return v___x_510_;
}
else
{
lean_object* v_pos_511_; lean_object* v_err_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_y_505_);
v_pos_511_ = lean_ctor_get(v___x_507_, 0);
v_err_512_ = lean_ctor_get(v___x_507_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_507_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_err_512_);
lean_inc(v_pos_511_);
lean_dec(v___x_507_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_pos_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_err_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg(){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___redArg___closed__9));
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad___redArg___boxed(lean_object* v___dummy_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Internal_Parsec_instMonad___redArg();
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instMonad(lean_object* v_00_u03b9_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___redArg___closed__9));
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___redArg(lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_p_547_, lean_object* v_q_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_550_; 
lean_inc(v_a_549_);
v___x_550_ = lean_apply_1(v_p_547_, v_a_549_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_dec(v_a_549_);
lean_dec_ref(v_q_548_);
lean_dec_ref(v_inst_546_);
lean_dec_ref(v_inst_545_);
return v___x_550_;
}
else
{
lean_object* v_pos_551_; lean_object* v_pos_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_pos_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc_n(v_pos_551_, 2);
v_pos_552_ = lean_ctor_get(v_inst_546_, 0);
lean_inc_n(v_pos_552_, 2);
lean_dec_ref(v_inst_546_);
v___x_553_ = lean_apply_1(v_pos_552_, v_a_549_);
v___x_554_ = lean_apply_1(v_pos_552_, v_pos_551_);
v___x_555_ = lean_apply_2(v_inst_545_, v___x_553_, v___x_554_);
v___x_556_ = lean_unbox(v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v_pos_551_);
lean_dec_ref(v_q_548_);
return v___x_550_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref_known(v___x_550_, 2);
v___x_557_ = lean_box(0);
v___x_558_ = lean_apply_2(v_q_548_, v___x_557_, v_pos_551_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b9_560_, lean_object* v_elem_561_, lean_object* v_idx_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_p_566_, lean_object* v_q_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_569_; 
lean_inc(v_a_568_);
v___x_569_ = lean_apply_1(v_p_566_, v_a_568_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_dec(v_a_568_);
lean_dec_ref(v_q_567_);
lean_dec_ref(v_inst_565_);
lean_dec_ref(v_inst_563_);
return v___x_569_;
}
else
{
lean_object* v_pos_570_; lean_object* v_pos_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_pos_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_n(v_pos_570_, 2);
v_pos_571_ = lean_ctor_get(v_inst_565_, 0);
lean_inc_n(v_pos_571_, 2);
lean_dec_ref(v_inst_565_);
v___x_572_ = lean_apply_1(v_pos_571_, v_a_568_);
v___x_573_ = lean_apply_1(v_pos_571_, v_pos_570_);
v___x_574_ = lean_apply_2(v_inst_563_, v___x_572_, v___x_573_);
v___x_575_ = lean_unbox(v___x_574_);
if (v___x_575_ == 0)
{
lean_dec(v_pos_570_);
lean_dec_ref(v_q_567_);
return v___x_569_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref_known(v___x_569_, 2);
v___x_576_ = lean_box(0);
v___x_577_ = lean_apply_2(v_q_567_, v___x_576_, v_pos_570_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_orElse___boxed(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b9_579_, lean_object* v_elem_580_, lean_object* v_idx_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_p_585_, lean_object* v_q_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_Internal_Parsec_orElse(v_00_u03b1_578_, v_00_u03b9_579_, v_elem_580_, v_idx_581_, v_inst_582_, v_inst_583_, v_inst_584_, v_p_585_, v_q_586_, v_a_587_);
lean_dec_ref(v_inst_583_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt___redArg(lean_object* v_p_589_, lean_object* v_it_590_){
_start:
{
lean_object* v___x_591_; 
lean_inc(v_it_590_);
v___x_591_ = lean_apply_1(v_p_589_, v_it_590_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_dec(v_it_590_);
return v___x_591_;
}
else
{
lean_object* v_err_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_err_592_ = lean_ctor_get(v___x_591_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_600_);
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_err_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_it_590_);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_it_590_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_err_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_attempt(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b9_602_, lean_object* v_p_603_, lean_object* v_it_604_){
_start:
{
lean_object* v___x_605_; 
lean_inc(v_it_604_);
v___x_605_ = lean_apply_1(v_p_603_, v_it_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_dec(v_it_604_);
return v___x_605_;
}
else
{
lean_object* v_err_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_err_606_ = lean_ctor_get(v___x_605_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_605_, 0);
lean_dec(v_unused_614_);
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_err_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_it_604_);
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_it_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_err_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__0(lean_object* v_00_u03b1_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1));
v___x_618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_618_, 0, v___y_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg___lam__1(lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_00_u03b1_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_625_; 
lean_inc(v___y_624_);
v___x_625_ = lean_apply_1(v___y_622_, v___y_624_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec_ref(v_inst_620_);
lean_dec_ref(v_inst_619_);
return v___x_625_;
}
else
{
lean_object* v_pos_626_; lean_object* v_pos_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_pos_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc_n(v_pos_626_, 2);
v_pos_627_ = lean_ctor_get(v_inst_619_, 0);
lean_inc_n(v_pos_627_, 2);
lean_dec_ref(v_inst_619_);
v___x_628_ = lean_apply_1(v_pos_627_, v___y_624_);
v___x_629_ = lean_apply_1(v_pos_627_, v_pos_626_);
v___x_630_ = lean_apply_2(v_inst_620_, v___x_628_, v___x_629_);
v___x_631_ = lean_unbox(v___x_630_);
if (v___x_631_ == 0)
{
lean_dec(v_pos_626_);
lean_dec_ref(v___y_623_);
return v___x_625_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref_known(v___x_625_, 2);
v___x_632_ = lean_box(0);
v___x_633_ = lean_apply_2(v___y_623_, v___x_632_, v_pos_626_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___redArg(lean_object* v_inst_635_, lean_object* v_inst_636_){
_start:
{
lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___f_637_ = ((lean_object*)(l_Std_Internal_Parsec_instAlternative___redArg___closed__0));
v___f_638_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___redArg___lam__1), 6, 2);
lean_closure_set(v___f_638_, 0, v_inst_636_);
lean_closure_set(v___f_638_, 1, v_inst_635_);
v___x_639_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___redArg___closed__7));
v___x_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___f_637_);
lean_ctor_set(v___x_640_, 2, v___f_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative(lean_object* v_00_u03b9_641_, lean_object* v_elem_642_, lean_object* v_idx_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_inst_646_){
_start:
{
lean_object* v___f_647_; lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___f_647_ = ((lean_object*)(l_Std_Internal_Parsec_instAlternative___redArg___closed__0));
v___f_648_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_instAlternative___redArg___lam__1), 6, 2);
lean_closure_set(v___f_648_, 0, v_inst_646_);
lean_closure_set(v___f_648_, 1, v_inst_644_);
v___x_649_ = ((lean_object*)(l_Std_Internal_Parsec_instMonad___redArg___closed__7));
v___x_650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v___f_647_);
lean_ctor_set(v___x_650_, 2, v___f_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_instAlternative___boxed(lean_object* v_00_u03b9_651_, lean_object* v_elem_652_, lean_object* v_idx_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Internal_Parsec_instAlternative(v_00_u03b9_651_, v_elem_652_, v_idx_653_, v_inst_654_, v_inst_655_, v_inst_656_);
lean_dec_ref(v_inst_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___redArg(lean_object* v_inst_661_, lean_object* v_it_662_){
_start:
{
lean_object* v_hasNext_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_hasNext_663_ = lean_ctor_get(v_inst_661_, 3);
lean_inc_ref(v_hasNext_663_);
lean_dec_ref(v_inst_661_);
lean_inc(v_it_662_);
v___x_664_ = lean_apply_1(v_hasNext_663_, v_it_662_);
v___x_665_ = lean_unbox(v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_it_662_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_Std_Internal_Parsec_eof___redArg___closed__1));
v___x_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_669_, 0, v_it_662_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof(lean_object* v_00_u03b9_670_, lean_object* v_elem_671_, lean_object* v_idx_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_it_676_){
_start:
{
lean_object* v_hasNext_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_hasNext_677_ = lean_ctor_get(v_inst_675_, 3);
lean_inc_ref(v_hasNext_677_);
lean_dec_ref(v_inst_675_);
lean_inc(v_it_676_);
v___x_678_ = lean_apply_1(v_hasNext_677_, v_it_676_);
v___x_679_ = lean_unbox(v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_it_676_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Std_Internal_Parsec_eof___redArg___closed__1));
v___x_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_683_, 0, v_it_676_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_eof___boxed(lean_object* v_00_u03b9_684_, lean_object* v_elem_685_, lean_object* v_idx_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_it_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_Internal_Parsec_eof(v_00_u03b9_684_, v_elem_685_, v_idx_686_, v_inst_687_, v_inst_688_, v_inst_689_, v_it_690_);
lean_dec_ref(v_inst_688_);
lean_dec_ref(v_inst_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___redArg(lean_object* v_inst_692_, lean_object* v_it_693_){
_start:
{
lean_object* v_hasNext_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_hasNext_694_ = lean_ctor_get(v_inst_692_, 3);
lean_inc_ref(v_hasNext_694_);
lean_dec_ref(v_inst_692_);
lean_inc(v_it_693_);
v___x_695_ = lean_apply_1(v_hasNext_694_, v_it_693_);
v___x_696_ = lean_unbox(v___x_695_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = 1;
v___x_698_ = lean_box(v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v_it_693_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
return v___x_699_;
}
else
{
uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = 0;
v___x_701_ = lean_box(v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_it_693_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof(lean_object* v_00_u03b9_703_, lean_object* v_elem_704_, lean_object* v_idx_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_it_709_){
_start:
{
lean_object* v_hasNext_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_hasNext_710_ = lean_ctor_get(v_inst_708_, 3);
lean_inc_ref(v_hasNext_710_);
lean_dec_ref(v_inst_708_);
lean_inc(v_it_709_);
v___x_711_ = lean_apply_1(v_hasNext_710_, v_it_709_);
v___x_712_ = lean_unbox(v___x_711_);
if (v___x_712_ == 0)
{
uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = 1;
v___x_714_ = lean_box(v___x_713_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_it_709_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
return v___x_715_;
}
else
{
uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = 0;
v___x_717_ = lean_box(v___x_716_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_it_709_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_isEof___boxed(lean_object* v_00_u03b9_719_, lean_object* v_elem_720_, lean_object* v_idx_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_it_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Std_Internal_Parsec_isEof(v_00_u03b9_719_, v_elem_720_, v_idx_721_, v_inst_722_, v_inst_723_, v_inst_724_, v_it_725_);
lean_dec_ref(v_inst_723_);
lean_dec_ref(v_inst_722_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___redArg(lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_p_729_, lean_object* v_acc_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_732_; 
lean_inc_ref(v_p_729_);
lean_inc(v_a_731_);
v___x_732_ = lean_apply_1(v_p_729_, v_a_731_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_pos_733_; lean_object* v_res_734_; lean_object* v___x_735_; 
lean_dec(v_a_731_);
v_pos_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_pos_733_);
v_res_734_ = lean_ctor_get(v___x_732_, 1);
lean_inc(v_res_734_);
lean_dec_ref_known(v___x_732_, 2);
v___x_735_ = lean_array_push(v_acc_730_, v_res_734_);
v_acc_730_ = v___x_735_;
v_a_731_ = v_pos_733_;
goto _start;
}
else
{
lean_object* v_pos_737_; lean_object* v_err_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v_p_729_);
v_pos_737_ = lean_ctor_get(v___x_732_, 0);
v_err_738_ = lean_ctor_get(v___x_732_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_753_ == 0)
{
v___x_740_ = v___x_732_;
v_isShared_741_ = v_isSharedCheck_753_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_err_738_);
lean_inc(v_pos_737_);
lean_dec(v___x_732_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_753_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_pos_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_pos_742_ = lean_ctor_get(v_inst_728_, 0);
lean_inc_n(v_pos_742_, 2);
lean_dec_ref(v_inst_728_);
v___x_743_ = lean_apply_1(v_pos_742_, v_a_731_);
lean_inc(v_pos_737_);
v___x_744_ = lean_apply_1(v_pos_742_, v_pos_737_);
v___x_745_ = lean_apply_2(v_inst_727_, v___x_743_, v___x_744_);
v___x_746_ = lean_unbox(v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_748_; 
lean_dec_ref(v_acc_730_);
if (v_isShared_741_ == 0)
{
v___x_748_ = v___x_740_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_pos_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_err_738_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
lean_object* v___x_751_; 
lean_dec(v_err_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 0);
lean_ctor_set(v___x_740_, 1, v_acc_730_);
v___x_751_ = v___x_740_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_pos_737_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_acc_730_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore(lean_object* v_00_u03b1_754_, lean_object* v_00_u03b9_755_, lean_object* v_elem_756_, lean_object* v_idx_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_p_761_, lean_object* v_acc_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_758_, v_inst_760_, v_p_761_, v_acc_762_, v_a_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___boxed(lean_object* v_00_u03b1_765_, lean_object* v_00_u03b9_766_, lean_object* v_elem_767_, lean_object* v_idx_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_p_772_, lean_object* v_acc_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_Internal_Parsec_manyCore(v_00_u03b1_765_, v_00_u03b9_766_, v_elem_767_, v_idx_768_, v_inst_769_, v_inst_770_, v_inst_771_, v_p_772_, v_acc_773_, v_a_774_);
lean_dec_ref(v_inst_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___redArg(lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_p_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Std_Internal_Parsec_many___redArg___closed__0));
v___x_783_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_778_, v_inst_779_, v_p_780_, v___x_782_, v_a_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many(lean_object* v_00_u03b1_784_, lean_object* v_00_u03b9_785_, lean_object* v_elem_786_, lean_object* v_idx_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_p_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Std_Internal_Parsec_many___redArg___closed__0));
v___x_794_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_788_, v_inst_790_, v_p_791_, v___x_793_, v_a_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many___boxed(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b9_796_, lean_object* v_elem_797_, lean_object* v_idx_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_p_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_Internal_Parsec_many(v_00_u03b1_795_, v_00_u03b9_796_, v_elem_797_, v_idx_798_, v_inst_799_, v_inst_800_, v_inst_801_, v_p_802_, v_a_803_);
lean_dec_ref(v_inst_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___redArg(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_p_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___x_809_; 
lean_inc_ref(v_p_807_);
v___x_809_ = lean_apply_1(v_p_807_, v_a_808_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_pos_810_; lean_object* v_res_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_pos_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_pos_810_);
v_res_811_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_res_811_);
lean_dec_ref_known(v___x_809_, 2);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_mk_empty_array_with_capacity(v___x_812_);
v___x_814_ = lean_array_push(v___x_813_, v_res_811_);
v___x_815_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_805_, v_inst_806_, v_p_807_, v___x_814_, v_pos_810_);
return v___x_815_;
}
else
{
lean_object* v_pos_816_; lean_object* v_err_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_p_807_);
lean_dec_ref(v_inst_806_);
lean_dec_ref(v_inst_805_);
v_pos_816_ = lean_ctor_get(v___x_809_, 0);
v_err_817_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_809_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_err_817_);
lean_inc(v_pos_816_);
lean_dec(v___x_809_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_pos_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_err_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b9_826_, lean_object* v_elem_827_, lean_object* v_idx_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_p_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_834_; 
lean_inc_ref(v_p_832_);
v___x_834_ = lean_apply_1(v_p_832_, v_a_833_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_pos_835_; lean_object* v_res_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_pos_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_pos_835_);
v_res_836_ = lean_ctor_get(v___x_834_, 1);
lean_inc(v_res_836_);
lean_dec_ref_known(v___x_834_, 2);
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_mk_empty_array_with_capacity(v___x_837_);
v___x_839_ = lean_array_push(v___x_838_, v_res_836_);
v___x_840_ = l_Std_Internal_Parsec_manyCore___redArg(v_inst_829_, v_inst_831_, v_p_832_, v___x_839_, v_pos_835_);
return v___x_840_;
}
else
{
lean_object* v_pos_841_; lean_object* v_err_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v_p_832_);
lean_dec_ref(v_inst_831_);
lean_dec_ref(v_inst_829_);
v_pos_841_ = lean_ctor_get(v___x_834_, 0);
v_err_842_ = lean_ctor_get(v___x_834_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_834_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_err_842_);
lean_inc(v_pos_841_);
lean_dec(v___x_834_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_pos_841_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_err_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1___boxed(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b9_851_, lean_object* v_elem_852_, lean_object* v_idx_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_p_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_Internal_Parsec_many1(v_00_u03b1_850_, v_00_u03b9_851_, v_elem_852_, v_idx_853_, v_inst_854_, v_inst_855_, v_inst_856_, v_p_857_, v_a_858_);
lean_dec_ref(v_inst_855_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___redArg(lean_object* v_inst_860_, lean_object* v_it_861_){
_start:
{
lean_object* v_hasNext_862_; lean_object* v_next_x27_863_; lean_object* v_curr_x27_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_hasNext_862_ = lean_ctor_get(v_inst_860_, 3);
lean_inc_ref(v_hasNext_862_);
v_next_x27_863_ = lean_ctor_get(v_inst_860_, 4);
lean_inc(v_next_x27_863_);
v_curr_x27_864_ = lean_ctor_get(v_inst_860_, 5);
lean_inc(v_curr_x27_864_);
lean_dec_ref(v_inst_860_);
lean_inc(v_it_861_);
v___x_865_ = lean_apply_1(v_hasNext_862_, v_it_861_);
v___x_866_ = lean_unbox(v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec(v_curr_x27_864_);
lean_dec(v_next_x27_863_);
v___x_867_ = lean_box(0);
v___x_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_868_, 0, v_it_861_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
return v___x_868_;
}
else
{
lean_object* v_c_869_; lean_object* v_it_x27_870_; lean_object* v___x_871_; 
lean_inc(v_it_861_);
v_c_869_ = lean_apply_2(v_curr_x27_864_, v_it_861_, lean_box(0));
v_it_x27_870_ = lean_apply_2(v_next_x27_863_, v_it_861_, lean_box(0));
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_it_x27_870_);
lean_ctor_set(v___x_871_, 1, v_c_869_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any(lean_object* v_00_u03b9_872_, lean_object* v_elem_873_, lean_object* v_idx_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_it_878_){
_start:
{
lean_object* v_hasNext_879_; lean_object* v_next_x27_880_; lean_object* v_curr_x27_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_hasNext_879_ = lean_ctor_get(v_inst_877_, 3);
lean_inc_ref(v_hasNext_879_);
v_next_x27_880_ = lean_ctor_get(v_inst_877_, 4);
lean_inc(v_next_x27_880_);
v_curr_x27_881_ = lean_ctor_get(v_inst_877_, 5);
lean_inc(v_curr_x27_881_);
lean_dec_ref(v_inst_877_);
lean_inc(v_it_878_);
v___x_882_ = lean_apply_1(v_hasNext_879_, v_it_878_);
v___x_883_ = lean_unbox(v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v_curr_x27_881_);
lean_dec(v_next_x27_880_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v_it_878_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
return v___x_885_;
}
else
{
lean_object* v_c_886_; lean_object* v_it_x27_887_; lean_object* v___x_888_; 
lean_inc(v_it_878_);
v_c_886_ = lean_apply_2(v_curr_x27_881_, v_it_878_, lean_box(0));
v_it_x27_887_ = lean_apply_2(v_next_x27_880_, v_it_878_, lean_box(0));
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v_it_x27_887_);
lean_ctor_set(v___x_888_, 1, v_c_886_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_any___boxed(lean_object* v_00_u03b9_889_, lean_object* v_elem_890_, lean_object* v_idx_891_, lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_it_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Std_Internal_Parsec_any(v_00_u03b9_889_, v_elem_890_, v_idx_891_, v_inst_892_, v_inst_893_, v_inst_894_, v_it_895_);
lean_dec_ref(v_inst_893_);
lean_dec_ref(v_inst_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___redArg(lean_object* v_inst_900_, lean_object* v_p_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_hasNext_903_; lean_object* v_next_x27_904_; lean_object* v_curr_x27_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_hasNext_903_ = lean_ctor_get(v_inst_900_, 3);
lean_inc_ref(v_hasNext_903_);
v_next_x27_904_ = lean_ctor_get(v_inst_900_, 4);
lean_inc(v_next_x27_904_);
v_curr_x27_905_ = lean_ctor_get(v_inst_900_, 5);
lean_inc(v_curr_x27_905_);
lean_dec_ref(v_inst_900_);
lean_inc(v_a_902_);
v___x_906_ = lean_apply_1(v_hasNext_903_, v_a_902_);
v___x_907_ = lean_unbox(v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec(v_curr_x27_905_);
lean_dec(v_next_x27_904_);
lean_dec_ref(v_p_901_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v_a_902_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
return v___x_909_;
}
else
{
lean_object* v_c_910_; lean_object* v_it_x27_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
lean_inc_n(v_a_902_, 2);
v_c_910_ = lean_apply_2(v_curr_x27_905_, v_a_902_, lean_box(0));
v_it_x27_911_ = lean_apply_2(v_next_x27_904_, v_a_902_, lean_box(0));
lean_inc(v_c_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_it_x27_911_);
lean_ctor_set(v___x_912_, 1, v_c_910_);
v___x_913_ = lean_apply_1(v_p_901_, v_c_910_);
v___x_914_ = lean_unbox(v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref_known(v___x_912_, 2);
v___x_915_ = ((lean_object*)(l_Std_Internal_Parsec_satisfy___redArg___closed__1));
v___x_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_916_, 0, v_a_902_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
return v___x_916_;
}
else
{
lean_dec(v_a_902_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy(lean_object* v_00_u03b9_917_, lean_object* v_elem_918_, lean_object* v_idx_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_p_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_hasNext_925_; lean_object* v_next_x27_926_; lean_object* v_curr_x27_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_hasNext_925_ = lean_ctor_get(v_inst_922_, 3);
lean_inc_ref(v_hasNext_925_);
v_next_x27_926_ = lean_ctor_get(v_inst_922_, 4);
lean_inc(v_next_x27_926_);
v_curr_x27_927_ = lean_ctor_get(v_inst_922_, 5);
lean_inc(v_curr_x27_927_);
lean_dec_ref(v_inst_922_);
lean_inc(v_a_924_);
v___x_928_ = lean_apply_1(v_hasNext_925_, v_a_924_);
v___x_929_ = lean_unbox(v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec(v_curr_x27_927_);
lean_dec(v_next_x27_926_);
lean_dec_ref(v_p_923_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_931_, 0, v_a_924_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
return v___x_931_;
}
else
{
lean_object* v_c_932_; lean_object* v_it_x27_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
lean_inc_n(v_a_924_, 2);
v_c_932_ = lean_apply_2(v_curr_x27_927_, v_a_924_, lean_box(0));
v_it_x27_933_ = lean_apply_2(v_next_x27_926_, v_a_924_, lean_box(0));
lean_inc(v_c_932_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_it_x27_933_);
lean_ctor_set(v___x_934_, 1, v_c_932_);
v___x_935_ = lean_apply_1(v_p_923_, v_c_932_);
v___x_936_ = lean_unbox(v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec_ref_known(v___x_934_, 2);
v___x_937_ = ((lean_object*)(l_Std_Internal_Parsec_satisfy___redArg___closed__1));
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v_a_924_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
return v___x_938_;
}
else
{
lean_dec(v_a_924_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___boxed(lean_object* v_00_u03b9_939_, lean_object* v_elem_940_, lean_object* v_idx_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_p_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_Internal_Parsec_satisfy(v_00_u03b9_939_, v_elem_940_, v_idx_941_, v_inst_942_, v_inst_943_, v_inst_944_, v_p_945_, v_a_946_);
lean_dec_ref(v_inst_943_);
lean_dec_ref(v_inst_942_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy___redArg(lean_object* v_p_948_, lean_object* v_it_949_){
_start:
{
lean_object* v___x_950_; 
lean_inc(v_it_949_);
v___x_950_ = lean_apply_1(v_p_948_, v_it_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_958_; 
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; 
v_unused_959_ = lean_ctor_get(v___x_950_, 1);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v___x_950_, 0);
lean_dec(v_unused_960_);
v___x_952_ = v___x_950_;
v_isShared_953_ = v_isSharedCheck_958_;
goto v_resetjp_951_;
}
else
{
lean_dec(v___x_950_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_958_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1));
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 1);
lean_ctor_set(v___x_952_, 1, v___x_954_);
lean_ctor_set(v___x_952_, 0, v_it_949_);
v___x_956_ = v___x_952_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_it_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
else
{
lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_969_ = lean_ctor_get(v___x_950_, 1);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v___x_950_, 0);
lean_dec(v_unused_970_);
v___x_962_ = v___x_950_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_dec(v___x_950_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_box(0);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 0);
lean_ctor_set(v___x_962_, 1, v___x_964_);
lean_ctor_set(v___x_962_, 0, v_it_949_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_it_949_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_notFollowedBy(lean_object* v_00_u03b1_971_, lean_object* v_00_u03b9_972_, lean_object* v_p_973_, lean_object* v_it_974_){
_start:
{
lean_object* v___x_975_; 
lean_inc(v_it_974_);
v___x_975_ = lean_apply_1(v_p_973_, v_it_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_983_; 
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; 
v_unused_984_ = lean_ctor_get(v___x_975_, 1);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v___x_975_, 0);
lean_dec(v_unused_985_);
v___x_977_ = v___x_975_;
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
else
{
lean_dec(v___x_975_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__1));
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 1);
lean_ctor_set(v___x_977_, 1, v___x_979_);
lean_ctor_set(v___x_977_, 0, v_it_974_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_it_974_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; lean_object* v_unused_995_; 
v_unused_994_ = lean_ctor_get(v___x_975_, 1);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v___x_975_, 0);
lean_dec(v_unused_995_);
v___x_987_ = v___x_975_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_975_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
lean_ctor_set(v___x_987_, 1, v___x_989_);
lean_ctor_set(v___x_987_, 0, v_it_974_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_it_974_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___redArg(lean_object* v_inst_996_, lean_object* v_it_997_){
_start:
{
lean_object* v_hasNext_998_; lean_object* v_curr_x27_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_hasNext_998_ = lean_ctor_get(v_inst_996_, 3);
lean_inc_ref(v_hasNext_998_);
v_curr_x27_999_ = lean_ctor_get(v_inst_996_, 5);
lean_inc(v_curr_x27_999_);
lean_dec_ref(v_inst_996_);
lean_inc(v_it_997_);
v___x_1000_ = lean_apply_1(v_hasNext_998_, v_it_997_);
v___x_1001_ = lean_unbox(v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v_curr_x27_999_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_it_997_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
return v___x_1003_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc(v_it_997_);
v___x_1004_ = lean_apply_2(v_curr_x27_999_, v_it_997_, lean_box(0));
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_it_997_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f(lean_object* v_00_u03b9_1007_, lean_object* v_elem_1008_, lean_object* v_idx_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_it_1013_){
_start:
{
lean_object* v_hasNext_1014_; lean_object* v_curr_x27_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_hasNext_1014_ = lean_ctor_get(v_inst_1012_, 3);
lean_inc_ref(v_hasNext_1014_);
v_curr_x27_1015_ = lean_ctor_get(v_inst_1012_, 5);
lean_inc(v_curr_x27_1015_);
lean_dec_ref(v_inst_1012_);
lean_inc(v_it_1013_);
v___x_1016_ = lean_apply_1(v_hasNext_1014_, v_it_1013_);
v___x_1017_ = lean_unbox(v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v_curr_x27_1015_);
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_it_1013_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_inc(v_it_1013_);
v___x_1020_ = lean_apply_2(v_curr_x27_1015_, v_it_1013_, lean_box(0));
v___x_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_it_1013_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x3f___boxed(lean_object* v_00_u03b9_1023_, lean_object* v_elem_1024_, lean_object* v_idx_1025_, lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_it_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_Internal_Parsec_peek_x3f(v_00_u03b9_1023_, v_elem_1024_, v_idx_1025_, v_inst_1026_, v_inst_1027_, v_inst_1028_, v_it_1029_);
lean_dec_ref(v_inst_1027_);
lean_dec_ref(v_inst_1026_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___redArg(lean_object* v_inst_1031_, lean_object* v_p_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_hasNext_1034_; lean_object* v_curr_x27_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_hasNext_1034_ = lean_ctor_get(v_inst_1031_, 3);
lean_inc_ref(v_hasNext_1034_);
v_curr_x27_1035_ = lean_ctor_get(v_inst_1031_, 5);
lean_inc(v_curr_x27_1035_);
lean_dec_ref(v_inst_1031_);
lean_inc(v_a_1033_);
v___x_1036_ = lean_apply_1(v_hasNext_1034_, v_a_1033_);
v___x_1037_ = lean_unbox(v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v_curr_x27_1035_);
lean_dec_ref(v_p_1032_);
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1033_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_inc(v_a_1033_);
v___x_1040_ = lean_apply_2(v_curr_x27_1035_, v_a_1033_, lean_box(0));
lean_inc(v___x_1040_);
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
v___x_1042_ = lean_apply_1(v_p_1032_, v___x_1040_);
v___x_1043_ = lean_unbox(v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref_known(v___x_1041_, 1);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_a_1033_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_a_1033_);
lean_ctor_set(v___x_1046_, 1, v___x_1041_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f(lean_object* v_00_u03b9_1047_, lean_object* v_elem_1048_, lean_object* v_idx_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_p_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_hasNext_1055_; lean_object* v_curr_x27_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_hasNext_1055_ = lean_ctor_get(v_inst_1052_, 3);
lean_inc_ref(v_hasNext_1055_);
v_curr_x27_1056_ = lean_ctor_get(v_inst_1052_, 5);
lean_inc(v_curr_x27_1056_);
lean_dec_ref(v_inst_1052_);
lean_inc(v_a_1054_);
v___x_1057_ = lean_apply_1(v_hasNext_1055_, v_a_1054_);
v___x_1058_ = lean_unbox(v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_curr_x27_1056_);
lean_dec_ref(v_p_1053_);
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_a_1054_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
lean_inc(v_a_1054_);
v___x_1061_ = lean_apply_2(v_curr_x27_1056_, v_a_1054_, lean_box(0));
lean_inc(v___x_1061_);
v___x_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
v___x_1063_ = lean_apply_1(v_p_1053_, v___x_1061_);
v___x_1064_ = lean_unbox(v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref_known(v___x_1062_, 1);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_a_1054_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_a_1054_);
lean_ctor_set(v___x_1067_, 1, v___x_1062_);
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekWhen_x3f___boxed(lean_object* v_00_u03b9_1068_, lean_object* v_elem_1069_, lean_object* v_idx_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_p_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Std_Internal_Parsec_peekWhen_x3f(v_00_u03b9_1068_, v_elem_1069_, v_idx_1070_, v_inst_1071_, v_inst_1072_, v_inst_1073_, v_p_1074_, v_a_1075_);
lean_dec_ref(v_inst_1072_);
lean_dec_ref(v_inst_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___redArg(lean_object* v_inst_1077_, lean_object* v_it_1078_){
_start:
{
lean_object* v_hasNext_1079_; lean_object* v_curr_x27_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_hasNext_1079_ = lean_ctor_get(v_inst_1077_, 3);
lean_inc_ref(v_hasNext_1079_);
v_curr_x27_1080_ = lean_ctor_get(v_inst_1077_, 5);
lean_inc(v_curr_x27_1080_);
lean_dec_ref(v_inst_1077_);
lean_inc(v_it_1078_);
v___x_1081_ = lean_apply_1(v_hasNext_1079_, v_it_1078_);
v___x_1082_ = lean_unbox(v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_curr_x27_1080_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_it_1078_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_inc(v_it_1078_);
v___x_1085_ = lean_apply_2(v_curr_x27_1080_, v_it_1078_, lean_box(0));
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_it_1078_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21(lean_object* v_00_u03b9_1087_, lean_object* v_elem_1088_, lean_object* v_idx_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_it_1093_){
_start:
{
lean_object* v_hasNext_1094_; lean_object* v_curr_x27_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_hasNext_1094_ = lean_ctor_get(v_inst_1092_, 3);
lean_inc_ref(v_hasNext_1094_);
v_curr_x27_1095_ = lean_ctor_get(v_inst_1092_, 5);
lean_inc(v_curr_x27_1095_);
lean_dec_ref(v_inst_1092_);
lean_inc(v_it_1093_);
v___x_1096_ = lean_apply_1(v_hasNext_1094_, v_it_1093_);
v___x_1097_ = lean_unbox(v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v_curr_x27_1095_);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_it_1093_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_inc(v_it_1093_);
v___x_1100_ = lean_apply_2(v_curr_x27_1095_, v_it_1093_, lean_box(0));
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_it_1093_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peek_x21___boxed(lean_object* v_00_u03b9_1102_, lean_object* v_elem_1103_, lean_object* v_idx_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_it_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_Internal_Parsec_peek_x21(v_00_u03b9_1102_, v_elem_1103_, v_idx_1104_, v_inst_1105_, v_inst_1106_, v_inst_1107_, v_it_1108_);
lean_dec_ref(v_inst_1106_);
lean_dec_ref(v_inst_1105_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___redArg(lean_object* v_inst_1110_, lean_object* v_default_1111_, lean_object* v_it_1112_){
_start:
{
lean_object* v_hasNext_1113_; lean_object* v_curr_x27_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_hasNext_1113_ = lean_ctor_get(v_inst_1110_, 3);
lean_inc_ref(v_hasNext_1113_);
v_curr_x27_1114_ = lean_ctor_get(v_inst_1110_, 5);
lean_inc(v_curr_x27_1114_);
lean_dec_ref(v_inst_1110_);
lean_inc(v_it_1112_);
v___x_1115_ = lean_apply_1(v_hasNext_1113_, v_it_1112_);
v___x_1116_ = lean_unbox(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec(v_curr_x27_1114_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_it_1112_);
lean_ctor_set(v___x_1117_, 1, v_default_1111_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec(v_default_1111_);
lean_inc(v_it_1112_);
v___x_1118_ = lean_apply_2(v_curr_x27_1114_, v_it_1112_, lean_box(0));
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_it_1112_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD(lean_object* v_00_u03b9_1120_, lean_object* v_elem_1121_, lean_object* v_idx_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_default_1126_, lean_object* v_it_1127_){
_start:
{
lean_object* v_hasNext_1128_; lean_object* v_curr_x27_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_hasNext_1128_ = lean_ctor_get(v_inst_1125_, 3);
lean_inc_ref(v_hasNext_1128_);
v_curr_x27_1129_ = lean_ctor_get(v_inst_1125_, 5);
lean_inc(v_curr_x27_1129_);
lean_dec_ref(v_inst_1125_);
lean_inc(v_it_1127_);
v___x_1130_ = lean_apply_1(v_hasNext_1128_, v_it_1127_);
v___x_1131_ = lean_unbox(v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec(v_curr_x27_1129_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_it_1127_);
lean_ctor_set(v___x_1132_, 1, v_default_1126_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_default_1126_);
lean_inc(v_it_1127_);
v___x_1133_ = lean_apply_2(v_curr_x27_1129_, v_it_1127_, lean_box(0));
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_it_1127_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_peekD___boxed(lean_object* v_00_u03b9_1135_, lean_object* v_elem_1136_, lean_object* v_idx_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_default_1141_, lean_object* v_it_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Std_Internal_Parsec_peekD(v_00_u03b9_1135_, v_elem_1136_, v_idx_1137_, v_inst_1138_, v_inst_1139_, v_inst_1140_, v_default_1141_, v_it_1142_);
lean_dec_ref(v_inst_1139_);
lean_dec_ref(v_inst_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___redArg(lean_object* v_inst_1144_, lean_object* v_it_1145_){
_start:
{
lean_object* v_hasNext_1146_; lean_object* v_next_x27_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_hasNext_1146_ = lean_ctor_get(v_inst_1144_, 3);
lean_inc_ref(v_hasNext_1146_);
v_next_x27_1147_ = lean_ctor_get(v_inst_1144_, 4);
lean_inc(v_next_x27_1147_);
lean_dec_ref(v_inst_1144_);
lean_inc(v_it_1145_);
v___x_1148_ = lean_apply_1(v_hasNext_1146_, v_it_1145_);
v___x_1149_ = lean_unbox(v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v_next_x27_1147_);
v___x_1150_ = lean_box(0);
v___x_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_it_1145_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_apply_2(v_next_x27_1147_, v_it_1145_, lean_box(0));
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip(lean_object* v_00_u03b9_1155_, lean_object* v_elem_1156_, lean_object* v_idx_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_it_1161_){
_start:
{
lean_object* v_hasNext_1162_; lean_object* v_next_x27_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_hasNext_1162_ = lean_ctor_get(v_inst_1160_, 3);
lean_inc_ref(v_hasNext_1162_);
v_next_x27_1163_ = lean_ctor_get(v_inst_1160_, 4);
lean_inc(v_next_x27_1163_);
lean_dec_ref(v_inst_1160_);
lean_inc(v_it_1161_);
v___x_1164_ = lean_apply_1(v_hasNext_1162_, v_it_1161_);
v___x_1165_ = lean_unbox(v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec(v_next_x27_1163_);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_it_1161_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_apply_2(v_next_x27_1163_, v_it_1161_, lean_box(0));
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_skip___boxed(lean_object* v_00_u03b9_1171_, lean_object* v_elem_1172_, lean_object* v_idx_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_it_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Std_Internal_Parsec_skip(v_00_u03b9_1171_, v_elem_1172_, v_idx_1173_, v_inst_1174_, v_inst_1175_, v_inst_1176_, v_it_1177_);
lean_dec_ref(v_inst_1175_);
lean_dec_ref(v_inst_1174_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___redArg(lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_p_1181_, lean_object* v_acc_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1184_; 
lean_inc_ref(v_p_1181_);
lean_inc(v_a_1183_);
v___x_1184_ = lean_apply_1(v_p_1181_, v_a_1183_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_pos_1185_; lean_object* v_res_1186_; uint32_t v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v_a_1183_);
v_pos_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_pos_1185_);
v_res_1186_ = lean_ctor_get(v___x_1184_, 1);
lean_inc(v_res_1186_);
lean_dec_ref_known(v___x_1184_, 2);
v___x_1187_ = lean_unbox_uint32(v_res_1186_);
lean_dec(v_res_1186_);
v___x_1188_ = lean_string_push(v_acc_1182_, v___x_1187_);
v_acc_1182_ = v___x_1188_;
v_a_1183_ = v_pos_1185_;
goto _start;
}
else
{
lean_object* v_pos_1190_; lean_object* v_err_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_p_1181_);
v_pos_1190_ = lean_ctor_get(v___x_1184_, 0);
v_err_1191_ = lean_ctor_get(v___x_1184_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1193_ = v___x_1184_;
v_isShared_1194_ = v_isSharedCheck_1206_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_err_1191_);
lean_inc(v_pos_1190_);
lean_dec(v___x_1184_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1206_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_pos_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_pos_1195_ = lean_ctor_get(v_inst_1180_, 0);
lean_inc_n(v_pos_1195_, 2);
lean_dec_ref(v_inst_1180_);
v___x_1196_ = lean_apply_1(v_pos_1195_, v_a_1183_);
lean_inc(v_pos_1190_);
v___x_1197_ = lean_apply_1(v_pos_1195_, v_pos_1190_);
v___x_1198_ = lean_apply_2(v_inst_1179_, v___x_1196_, v___x_1197_);
v___x_1199_ = lean_unbox(v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1201_; 
lean_dec_ref(v_acc_1182_);
if (v_isShared_1194_ == 0)
{
v___x_1201_ = v___x_1193_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_pos_1190_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_err_1191_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v___x_1204_; 
lean_dec(v_err_1191_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 0);
lean_ctor_set(v___x_1193_, 1, v_acc_1182_);
v___x_1204_ = v___x_1193_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_pos_1190_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_acc_1182_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore(lean_object* v_00_u03b9_1207_, lean_object* v_elem_1208_, lean_object* v_idx_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_p_1213_, lean_object* v_acc_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1210_, v_inst_1212_, v_p_1213_, v_acc_1214_, v_a_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___boxed(lean_object* v_00_u03b9_1217_, lean_object* v_elem_1218_, lean_object* v_idx_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_p_1223_, lean_object* v_acc_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_Internal_Parsec_manyCharsCore(v_00_u03b9_1217_, v_elem_1218_, v_idx_1219_, v_inst_1220_, v_inst_1221_, v_inst_1222_, v_p_1223_, v_acc_1224_, v_a_1225_);
lean_dec_ref(v_inst_1221_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___redArg(lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_p_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0));
v___x_1232_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1227_, v_inst_1228_, v_p_1229_, v___x_1231_, v_a_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars(lean_object* v_00_u03b9_1233_, lean_object* v_elem_1234_, lean_object* v_idx_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_p_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0));
v___x_1242_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1236_, v_inst_1238_, v_p_1239_, v___x_1241_, v_a_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyChars___boxed(lean_object* v_00_u03b9_1243_, lean_object* v_elem_1244_, lean_object* v_idx_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_p_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_Internal_Parsec_manyChars(v_00_u03b9_1243_, v_elem_1244_, v_idx_1245_, v_inst_1246_, v_inst_1247_, v_inst_1248_, v_p_1249_, v_a_1250_);
lean_dec_ref(v_inst_1247_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___redArg(lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_p_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v___x_1256_; 
lean_inc_ref(v_p_1254_);
v___x_1256_ = lean_apply_1(v_p_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_pos_1257_; lean_object* v_res_1258_; lean_object* v___x_1259_; uint32_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_pos_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_pos_1257_);
v_res_1258_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_res_1258_);
lean_dec_ref_known(v___x_1256_, 2);
v___x_1259_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0));
v___x_1260_ = lean_unbox_uint32(v_res_1258_);
lean_dec(v_res_1258_);
v___x_1261_ = lean_string_push(v___x_1259_, v___x_1260_);
v___x_1262_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1252_, v_inst_1253_, v_p_1254_, v___x_1261_, v_pos_1257_);
return v___x_1262_;
}
else
{
lean_object* v_pos_1263_; lean_object* v_err_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_p_1254_);
lean_dec_ref(v_inst_1253_);
lean_dec_ref(v_inst_1252_);
v_pos_1263_ = lean_ctor_get(v___x_1256_, 0);
v_err_1264_ = lean_ctor_get(v___x_1256_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1256_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_err_1264_);
lean_inc(v_pos_1263_);
lean_dec(v___x_1256_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_pos_1263_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_err_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars(lean_object* v_00_u03b9_1272_, lean_object* v_elem_1273_, lean_object* v_idx_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_p_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___x_1280_; 
lean_inc_ref(v_p_1278_);
v___x_1280_ = lean_apply_1(v_p_1278_, v_a_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_pos_1281_; lean_object* v_res_1282_; lean_object* v___x_1283_; uint32_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_pos_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_pos_1281_);
v_res_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_res_1282_);
lean_dec_ref_known(v___x_1280_, 2);
v___x_1283_ = ((lean_object*)(l_Std_Internal_Parsec_instInhabited___redArg___lam__0___closed__0));
v___x_1284_ = lean_unbox_uint32(v_res_1282_);
lean_dec(v_res_1282_);
v___x_1285_ = lean_string_push(v___x_1283_, v___x_1284_);
v___x_1286_ = l_Std_Internal_Parsec_manyCharsCore___redArg(v_inst_1275_, v_inst_1277_, v_p_1278_, v___x_1285_, v_pos_1281_);
return v___x_1286_;
}
else
{
lean_object* v_pos_1287_; lean_object* v_err_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_p_1278_);
lean_dec_ref(v_inst_1277_);
lean_dec_ref(v_inst_1275_);
v_pos_1287_ = lean_ctor_get(v___x_1280_, 0);
v_err_1288_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1280_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_err_1288_);
lean_inc(v_pos_1287_);
lean_dec(v___x_1280_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_pos_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_err_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_many1Chars___boxed(lean_object* v_00_u03b9_1296_, lean_object* v_elem_1297_, lean_object* v_idx_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_p_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_Internal_Parsec_many1Chars(v_00_u03b9_1296_, v_elem_1297_, v_idx_1298_, v_inst_1299_, v_inst_1300_, v_inst_1301_, v_p_1302_, v_a_1303_);
lean_dec_ref(v_inst_1300_);
return v_res_1304_;
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
