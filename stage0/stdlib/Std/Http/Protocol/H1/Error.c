// Lean compiler output
// Module: Std.Http.Protocol.H1.Error
// Imports: public import Std.Time public import Std.Http.Data public import Std.Http.Internal public import Std.Http.Protocol.H1.Parser public import Std.Http.Protocol.H1.Config public import Std.Http.Protocol.H1.Message
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidHeader_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidHeader_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_timeout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_timeout_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_entityTooLarge_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_entityTooLarge_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_uriTooLong_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_uriTooLong_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidChunk_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidChunk_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_connectionClosed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_connectionClosed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_badMessage_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_badMessage_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_headersTooLarge_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_headersTooLarge_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Http.Protocol.H1.Error.headersTooLarge"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Std.Http.Protocol.H1.Error.tooManyHeaders"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Http.Protocol.H1.Error.badMessage"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__4_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__5_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Std.Http.Protocol.H1.Error.connectionClosed"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__6_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Std.Http.Protocol.H1.Error.invalidChunk"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__8_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Std.Http.Protocol.H1.Error.unsupportedVersion"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__11_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Http.Protocol.H1.Error.uriTooLong"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__13_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Std.Http.Protocol.H1.Error.entityTooLarge"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__15 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__15_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Http.Protocol.H1.Error.timeout"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__16 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__17_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Http.Protocol.H1.Error.invalidHeader"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__19 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__19_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Std.Http.Protocol.H1.Error.invalidStatusLine"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__21 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__21_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__22;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__23;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Std.Http.Protocol.H1.Error.other"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__24 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__25 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__26 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__26_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprError_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprError_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instReprError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instReprError_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instReprError___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_instReprError = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instBEqError_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqError_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instBEqError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instBEqError_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instBEqError___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instBEqError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_instBEqError = (const lean_object*)&l_Std_Http_Protocol_H1_instBEqError___closed__0_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Invalid status line"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Invalid header"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Timeout"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Entity too large"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "URI too long"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unsupported version"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Invalid chunk"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Connection closed"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Bad message"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Too many headers"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Headers too large"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Other error: "};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instToStringError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_instToStringError = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
case 7:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
case 8:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(8u);
return v___x_10_;
}
case 9:
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(9u);
return v___x_11_;
}
case 10:
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(10u);
return v___x_12_;
}
default: 
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(11u);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorIdx___boxed(lean_object* v_x_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_14_);
lean_dec(v_x_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim___redArg(lean_object* v_t_16_, lean_object* v_k_17_){
_start:
{
if (lean_obj_tag(v_t_16_) == 11)
{
lean_object* v_message_18_; lean_object* v___x_19_; 
v_message_18_ = lean_ctor_get(v_t_16_, 0);
lean_inc_ref(v_message_18_);
lean_dec_ref(v_t_16_);
v___x_19_ = lean_apply_1(v_k_17_, v_message_18_);
return v___x_19_;
}
else
{
lean_dec(v_t_16_);
return v_k_17_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim___boxed(lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Http_Protocol_H1_Error_ctorElim(v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim___redArg(lean_object* v_t_32_, lean_object* v_invalidStatusLine_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_32_, v_invalidStatusLine_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_invalidStatusLine_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_36_, v_invalidStatusLine_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidHeader_elim___redArg(lean_object* v_t_40_, lean_object* v_invalidHeader_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_40_, v_invalidHeader_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidHeader_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_invalidHeader_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_44_, v_invalidHeader_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_timeout_elim___redArg(lean_object* v_t_48_, lean_object* v_timeout_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_48_, v_timeout_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_timeout_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_timeout_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_52_, v_timeout_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_entityTooLarge_elim___redArg(lean_object* v_t_56_, lean_object* v_entityTooLarge_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_56_, v_entityTooLarge_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_entityTooLarge_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_entityTooLarge_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_60_, v_entityTooLarge_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_uriTooLong_elim___redArg(lean_object* v_t_64_, lean_object* v_uriTooLong_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_64_, v_uriTooLong_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_uriTooLong_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_uriTooLong_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_68_, v_uriTooLong_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim___redArg(lean_object* v_t_72_, lean_object* v_unsupportedVersion_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_72_, v_unsupportedVersion_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_unsupportedVersion_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_76_, v_unsupportedVersion_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidChunk_elim___redArg(lean_object* v_t_80_, lean_object* v_invalidChunk_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_80_, v_invalidChunk_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidChunk_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_invalidChunk_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_84_, v_invalidChunk_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_connectionClosed_elim___redArg(lean_object* v_t_88_, lean_object* v_connectionClosed_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_88_, v_connectionClosed_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_connectionClosed_elim(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_connectionClosed_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_92_, v_connectionClosed_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_badMessage_elim___redArg(lean_object* v_t_96_, lean_object* v_badMessage_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_96_, v_badMessage_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_badMessage_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_badMessage_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_100_, v_badMessage_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim___redArg(lean_object* v_t_104_, lean_object* v_tooManyHeaders_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_104_, v_tooManyHeaders_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_tooManyHeaders_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_108_, v_tooManyHeaders_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_headersTooLarge_elim___redArg(lean_object* v_t_112_, lean_object* v_headersTooLarge_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_112_, v_headersTooLarge_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_headersTooLarge_elim(lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_headersTooLarge_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_116_, v_headersTooLarge_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_other_elim___redArg(lean_object* v_t_120_, lean_object* v_other_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_120_, v_other_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_other_elim(lean_object* v_motive_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_other_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_124_, v_other_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = lean_nat_to_int(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_to_int(v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprError_repr(lean_object* v_x_171_, lean_object* v_prec_172_){
_start:
{
lean_object* v___y_174_; lean_object* v___y_181_; lean_object* v___y_188_; lean_object* v___y_195_; lean_object* v___y_202_; lean_object* v___y_209_; lean_object* v___y_216_; lean_object* v___y_223_; lean_object* v___y_230_; lean_object* v___y_237_; lean_object* v___y_244_; 
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(1024u);
v___x_251_ = lean_nat_dec_le(v___x_250_, v_prec_172_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_244_ = v___x_252_;
goto v___jp_243_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_244_ = v___x_253_;
goto v___jp_243_;
}
}
case 1:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(1024u);
v___x_255_ = lean_nat_dec_le(v___x_254_, v_prec_172_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_237_ = v___x_256_;
goto v___jp_236_;
}
else
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_237_ = v___x_257_;
goto v___jp_236_;
}
}
case 2:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1024u);
v___x_259_ = lean_nat_dec_le(v___x_258_, v_prec_172_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_230_ = v___x_260_;
goto v___jp_229_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_230_ = v___x_261_;
goto v___jp_229_;
}
}
case 3:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_unsigned_to_nat(1024u);
v___x_263_ = lean_nat_dec_le(v___x_262_, v_prec_172_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_223_ = v___x_264_;
goto v___jp_222_;
}
else
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_223_ = v___x_265_;
goto v___jp_222_;
}
}
case 4:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1024u);
v___x_267_ = lean_nat_dec_le(v___x_266_, v_prec_172_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_216_ = v___x_268_;
goto v___jp_215_;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_216_ = v___x_269_;
goto v___jp_215_;
}
}
case 5:
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(1024u);
v___x_271_ = lean_nat_dec_le(v___x_270_, v_prec_172_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_209_ = v___x_272_;
goto v___jp_208_;
}
else
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_209_ = v___x_273_;
goto v___jp_208_;
}
}
case 6:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(1024u);
v___x_275_ = lean_nat_dec_le(v___x_274_, v_prec_172_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_202_ = v___x_276_;
goto v___jp_201_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_202_ = v___x_277_;
goto v___jp_201_;
}
}
case 7:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1024u);
v___x_279_ = lean_nat_dec_le(v___x_278_, v_prec_172_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_195_ = v___x_280_;
goto v___jp_194_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_195_ = v___x_281_;
goto v___jp_194_;
}
}
case 8:
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1024u);
v___x_283_ = lean_nat_dec_le(v___x_282_, v_prec_172_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_188_ = v___x_284_;
goto v___jp_187_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_188_ = v___x_285_;
goto v___jp_187_;
}
}
case 9:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(1024u);
v___x_287_ = lean_nat_dec_le(v___x_286_, v_prec_172_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_181_ = v___x_288_;
goto v___jp_180_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_181_ = v___x_289_;
goto v___jp_180_;
}
}
case 10:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(1024u);
v___x_291_ = lean_nat_dec_le(v___x_290_, v_prec_172_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_174_ = v___x_292_;
goto v___jp_173_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_174_ = v___x_293_;
goto v___jp_173_;
}
}
default: 
{
lean_object* v_message_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_314_; 
v_message_294_ = lean_ctor_get(v_x_171_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_314_ == 0)
{
v___x_296_ = v_x_171_;
v_isShared_297_ = v_isSharedCheck_314_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_message_294_);
lean_dec(v_x_171_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_314_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___y_299_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(1024u);
v___x_311_ = lean_nat_dec_le(v___x_310_, v_prec_172_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_299_ = v___x_312_;
goto v___jp_298_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_299_ = v___x_313_;
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_300_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__26));
v___x_301_ = l_String_quote(v_message_294_);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 3);
lean_ctor_set(v___x_296_, 0, v___x_301_);
v___x_303_ = v___x_296_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_309_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_300_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
lean_inc(v___y_299_);
v___x_305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_305_, 0, v___y_299_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = 0;
v___x_307_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*1, v___x_306_);
v___x_308_ = l_Repr_addAppParen(v___x_307_, v_prec_172_);
return v___x_308_;
}
}
}
}
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_175_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__1));
lean_inc(v___y_174_);
v___x_176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_176_, 0, v___y_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = 0;
v___x_178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*1, v___x_177_);
v___x_179_ = l_Repr_addAppParen(v___x_178_, v_prec_172_);
return v___x_179_;
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_182_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__3));
lean_inc(v___y_181_);
v___x_183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_183_, 0, v___y_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = 0;
v___x_185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_184_);
v___x_186_ = l_Repr_addAppParen(v___x_185_, v_prec_172_);
return v___x_186_;
}
v___jp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_189_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__5));
lean_inc(v___y_188_);
v___x_190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_190_, 0, v___y_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = 0;
v___x_192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_191_);
v___x_193_ = l_Repr_addAppParen(v___x_192_, v_prec_172_);
return v___x_193_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__7));
lean_inc(v___y_195_);
v___x_197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_197_, 0, v___y_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = 0;
v___x_199_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*1, v___x_198_);
v___x_200_ = l_Repr_addAppParen(v___x_199_, v_prec_172_);
return v___x_200_;
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_203_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__9));
lean_inc(v___y_202_);
v___x_204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_204_, 0, v___y_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = 0;
v___x_206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_205_);
v___x_207_ = l_Repr_addAppParen(v___x_206_, v_prec_172_);
return v___x_207_;
}
v___jp_208_:
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_210_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__11));
lean_inc(v___y_209_);
v___x_211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_211_, 0, v___y_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = 0;
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_212_);
v___x_214_ = l_Repr_addAppParen(v___x_213_, v_prec_172_);
return v___x_214_;
}
v___jp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_217_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__13));
lean_inc(v___y_216_);
v___x_218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_218_, 0, v___y_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = 0;
v___x_220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1, v___x_219_);
v___x_221_ = l_Repr_addAppParen(v___x_220_, v_prec_172_);
return v___x_221_;
}
v___jp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_224_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__15));
lean_inc(v___y_223_);
v___x_225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_225_, 0, v___y_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = 0;
v___x_227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1, v___x_226_);
v___x_228_ = l_Repr_addAppParen(v___x_227_, v_prec_172_);
return v___x_228_;
}
v___jp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_231_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__17));
lean_inc(v___y_230_);
v___x_232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_232_, 0, v___y_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = 0;
v___x_234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_233_);
v___x_235_ = l_Repr_addAppParen(v___x_234_, v_prec_172_);
return v___x_235_;
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_238_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__19));
lean_inc(v___y_237_);
v___x_239_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_239_, 0, v___y_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = 0;
v___x_241_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*1, v___x_240_);
v___x_242_ = l_Repr_addAppParen(v___x_241_, v_prec_172_);
return v___x_242_;
}
v___jp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_245_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__21));
lean_inc(v___y_244_);
v___x_246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_246_, 0, v___y_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = 0;
v___x_248_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*1, v___x_247_);
v___x_249_ = l_Repr_addAppParen(v___x_248_, v_prec_172_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprError_repr___boxed(lean_object* v_x_315_, lean_object* v_prec_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Http_Protocol_H1_instReprError_repr(v_x_315_, v_prec_316_);
lean_dec(v_prec_316_);
return v_res_317_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instBEqError_beq(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_322_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_320_);
v___x_323_ = l_Std_Http_Protocol_H1_Error_ctorIdx(v_x_321_);
v___x_324_ = lean_nat_dec_eq(v___x_322_, v___x_323_);
lean_dec(v___x_323_);
lean_dec(v___x_322_);
if (v___x_324_ == 0)
{
return v___x_324_;
}
else
{
if (lean_obj_tag(v_x_320_) == 11)
{
lean_object* v_message_325_; lean_object* v_message_326_; uint8_t v___x_327_; 
v_message_325_ = lean_ctor_get(v_x_320_, 0);
v_message_326_ = lean_ctor_get(v_x_321_, 0);
v___x_327_ = lean_string_dec_eq(v_message_325_, v_message_326_);
return v___x_327_;
}
else
{
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqError_beq___boxed(lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_x_328_, v_x_329_);
lean_dec(v_x_329_);
lean_dec(v_x_328_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0(lean_object* v_x_346_){
_start:
{
switch(lean_obj_tag(v_x_346_))
{
case 0:
{
lean_object* v___x_347_; 
v___x_347_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0));
return v___x_347_;
}
case 1:
{
lean_object* v___x_348_; 
v___x_348_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1));
return v___x_348_;
}
case 2:
{
lean_object* v___x_349_; 
v___x_349_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2));
return v___x_349_;
}
case 3:
{
lean_object* v___x_350_; 
v___x_350_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3));
return v___x_350_;
}
case 4:
{
lean_object* v___x_351_; 
v___x_351_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4));
return v___x_351_;
}
case 5:
{
lean_object* v___x_352_; 
v___x_352_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5));
return v___x_352_;
}
case 6:
{
lean_object* v___x_353_; 
v___x_353_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6));
return v___x_353_;
}
case 7:
{
lean_object* v___x_354_; 
v___x_354_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7));
return v___x_354_;
}
case 8:
{
lean_object* v___x_355_; 
v___x_355_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8));
return v___x_355_;
}
case 9:
{
lean_object* v___x_356_; 
v___x_356_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9));
return v___x_356_;
}
case 10:
{
lean_object* v___x_357_; 
v___x_357_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10));
return v___x_357_;
}
default: 
{
lean_object* v_message_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_message_358_ = lean_ctor_get(v_x_346_, 0);
v___x_359_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11));
v___x_360_ = lean_string_append(v___x_359_, v_message_358_);
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed(lean_object* v_x_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Http_Protocol_H1_instToStringError___lam__0(v_x_361_);
lean_dec(v_x_361_);
return v_res_362_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Http_Data(uint8_t builtin);
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Error(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Error(builtin);
}
#ifdef __cplusplus
}
#endif
