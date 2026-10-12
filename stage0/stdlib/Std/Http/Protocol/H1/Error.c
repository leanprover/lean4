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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Http_Protocol_H1_Error_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 11)
{
lean_object* v_message_7_; lean_object* v___x_8_; 
v_message_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_message_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_message_7_);
return v___x_8_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Http_Protocol_H1_Error_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim___redArg(lean_object* v_t_21_, lean_object* v_invalidStatusLine_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_21_, v_invalidStatusLine_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidStatusLine_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_invalidStatusLine_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_25_, v_invalidStatusLine_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidHeader_elim___redArg(lean_object* v_t_29_, lean_object* v_invalidHeader_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_29_, v_invalidHeader_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidHeader_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_invalidHeader_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_33_, v_invalidHeader_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_timeout_elim___redArg(lean_object* v_t_37_, lean_object* v_timeout_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_37_, v_timeout_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_timeout_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_timeout_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_41_, v_timeout_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_entityTooLarge_elim___redArg(lean_object* v_t_45_, lean_object* v_entityTooLarge_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_45_, v_entityTooLarge_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_entityTooLarge_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_entityTooLarge_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_49_, v_entityTooLarge_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_uriTooLong_elim___redArg(lean_object* v_t_53_, lean_object* v_uriTooLong_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_53_, v_uriTooLong_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_uriTooLong_elim(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_uriTooLong_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_57_, v_uriTooLong_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim___redArg(lean_object* v_t_61_, lean_object* v_unsupportedVersion_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_61_, v_unsupportedVersion_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedVersion_elim(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_unsupportedVersion_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_65_, v_unsupportedVersion_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidChunk_elim___redArg(lean_object* v_t_69_, lean_object* v_invalidChunk_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_69_, v_invalidChunk_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidChunk_elim(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_invalidChunk_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_73_, v_invalidChunk_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_connectionClosed_elim___redArg(lean_object* v_t_77_, lean_object* v_connectionClosed_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_77_, v_connectionClosed_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_connectionClosed_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_connectionClosed_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_81_, v_connectionClosed_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_badMessage_elim___redArg(lean_object* v_t_85_, lean_object* v_badMessage_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_85_, v_badMessage_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_badMessage_elim(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_badMessage_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_89_, v_badMessage_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim___redArg(lean_object* v_t_93_, lean_object* v_tooManyHeaders_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_93_, v_tooManyHeaders_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim(lean_object* v_motive_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_tooManyHeaders_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_97_, v_tooManyHeaders_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_headersTooLarge_elim___redArg(lean_object* v_t_101_, lean_object* v_headersTooLarge_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_101_, v_headersTooLarge_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_headersTooLarge_elim(lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_headersTooLarge_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_105_, v_headersTooLarge_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_other_elim___redArg(lean_object* v_t_109_, lean_object* v_other_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_109_, v_other_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_other_elim(lean_object* v_motive_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_other_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_113_, v_other_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(2u);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprError_repr(lean_object* v_x_160_, lean_object* v_prec_161_){
_start:
{
lean_object* v___y_163_; lean_object* v___y_170_; lean_object* v___y_177_; lean_object* v___y_184_; lean_object* v___y_191_; lean_object* v___y_198_; lean_object* v___y_205_; lean_object* v___y_212_; lean_object* v___y_219_; lean_object* v___y_226_; lean_object* v___y_233_; 
switch(lean_obj_tag(v_x_160_))
{
case 0:
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(1024u);
v___x_240_ = lean_nat_dec_le(v___x_239_, v_prec_161_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_233_ = v___x_241_;
goto v___jp_232_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_233_ = v___x_242_;
goto v___jp_232_;
}
}
case 1:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(1024u);
v___x_244_ = lean_nat_dec_le(v___x_243_, v_prec_161_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_226_ = v___x_245_;
goto v___jp_225_;
}
else
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_226_ = v___x_246_;
goto v___jp_225_;
}
}
case 2:
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_unsigned_to_nat(1024u);
v___x_248_ = lean_nat_dec_le(v___x_247_, v_prec_161_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
v___x_249_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_219_ = v___x_249_;
goto v___jp_218_;
}
else
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_219_ = v___x_250_;
goto v___jp_218_;
}
}
case 3:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(1024u);
v___x_252_ = lean_nat_dec_le(v___x_251_, v_prec_161_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_212_ = v___x_253_;
goto v___jp_211_;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_212_ = v___x_254_;
goto v___jp_211_;
}
}
case 4:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(1024u);
v___x_256_ = lean_nat_dec_le(v___x_255_, v_prec_161_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_205_ = v___x_257_;
goto v___jp_204_;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_205_ = v___x_258_;
goto v___jp_204_;
}
}
case 5:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1024u);
v___x_260_ = lean_nat_dec_le(v___x_259_, v_prec_161_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_198_ = v___x_261_;
goto v___jp_197_;
}
else
{
lean_object* v___x_262_; 
v___x_262_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_198_ = v___x_262_;
goto v___jp_197_;
}
}
case 6:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(1024u);
v___x_264_ = lean_nat_dec_le(v___x_263_, v_prec_161_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_191_ = v___x_265_;
goto v___jp_190_;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_191_ = v___x_266_;
goto v___jp_190_;
}
}
case 7:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1024u);
v___x_268_ = lean_nat_dec_le(v___x_267_, v_prec_161_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_184_ = v___x_269_;
goto v___jp_183_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_184_ = v___x_270_;
goto v___jp_183_;
}
}
case 8:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(1024u);
v___x_272_ = lean_nat_dec_le(v___x_271_, v_prec_161_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_177_ = v___x_273_;
goto v___jp_176_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_177_ = v___x_274_;
goto v___jp_176_;
}
}
case 9:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1024u);
v___x_276_ = lean_nat_dec_le(v___x_275_, v_prec_161_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_170_ = v___x_277_;
goto v___jp_169_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_170_ = v___x_278_;
goto v___jp_169_;
}
}
case 10:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1024u);
v___x_280_ = lean_nat_dec_le(v___x_279_, v_prec_161_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_163_ = v___x_281_;
goto v___jp_162_;
}
else
{
lean_object* v___x_282_; 
v___x_282_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_163_ = v___x_282_;
goto v___jp_162_;
}
}
default: 
{
lean_object* v_message_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_303_; 
v_message_283_ = lean_ctor_get(v_x_160_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_303_ == 0)
{
v___x_285_ = v_x_160_;
v_isShared_286_ = v_isSharedCheck_303_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_message_283_);
lean_dec(v_x_160_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_303_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___y_288_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1024u);
v___x_300_ = lean_nat_dec_le(v___x_299_, v_prec_161_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__22, &l_Std_Http_Protocol_H1_instReprError_repr___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__22);
v___y_288_ = v___x_301_;
goto v___jp_287_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__23, &l_Std_Http_Protocol_H1_instReprError_repr___closed__23_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__23);
v___y_288_ = v___x_302_;
goto v___jp_287_;
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_289_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__26));
v___x_290_ = l_String_quote(v_message_283_);
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 3);
lean_ctor_set(v___x_285_, 0, v___x_290_);
v___x_292_ = v___x_285_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_298_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_289_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_inc(v___y_288_);
v___x_294_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_294_, 0, v___y_288_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = 0;
v___x_296_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1, v___x_295_);
v___x_297_ = l_Repr_addAppParen(v___x_296_, v_prec_161_);
return v___x_297_;
}
}
}
}
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__1));
lean_inc(v___y_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
v___x_168_ = l_Repr_addAppParen(v___x_167_, v_prec_161_);
return v___x_168_;
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__3));
lean_inc(v___y_170_);
v___x_172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_172_, 0, v___y_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = 0;
v___x_174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*1, v___x_173_);
v___x_175_ = l_Repr_addAppParen(v___x_174_, v_prec_161_);
return v___x_175_;
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_178_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__5));
lean_inc(v___y_177_);
v___x_179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_179_, 0, v___y_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = 0;
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
v___x_182_ = l_Repr_addAppParen(v___x_181_, v_prec_161_);
return v___x_182_;
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_185_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__7));
lean_inc(v___y_184_);
v___x_186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_186_, 0, v___y_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = 0;
v___x_188_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*1, v___x_187_);
v___x_189_ = l_Repr_addAppParen(v___x_188_, v_prec_161_);
return v___x_189_;
}
v___jp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__9));
lean_inc(v___y_191_);
v___x_193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_193_, 0, v___y_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = 0;
v___x_195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_194_);
v___x_196_ = l_Repr_addAppParen(v___x_195_, v_prec_161_);
return v___x_196_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_199_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__11));
lean_inc(v___y_198_);
v___x_200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_200_, 0, v___y_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = 0;
v___x_202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*1, v___x_201_);
v___x_203_ = l_Repr_addAppParen(v___x_202_, v_prec_161_);
return v___x_203_;
}
v___jp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_206_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__13));
lean_inc(v___y_205_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = 0;
v___x_209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*1, v___x_208_);
v___x_210_ = l_Repr_addAppParen(v___x_209_, v_prec_161_);
return v___x_210_;
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_213_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__15));
lean_inc(v___y_212_);
v___x_214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_214_, 0, v___y_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = 0;
v___x_216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*1, v___x_215_);
v___x_217_ = l_Repr_addAppParen(v___x_216_, v_prec_161_);
return v___x_217_;
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_220_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__17));
lean_inc(v___y_219_);
v___x_221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_221_, 0, v___y_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = 0;
v___x_223_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v___x_222_);
v___x_224_ = l_Repr_addAppParen(v___x_223_, v_prec_161_);
return v___x_224_;
}
v___jp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_227_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__19));
lean_inc(v___y_226_);
v___x_228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_228_, 0, v___y_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = 0;
v___x_230_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*1, v___x_229_);
v___x_231_ = l_Repr_addAppParen(v___x_230_, v_prec_161_);
return v___x_231_;
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_234_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__21));
lean_inc(v___y_233_);
v___x_235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_235_, 0, v___y_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = 0;
v___x_237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_236_);
v___x_238_ = l_Repr_addAppParen(v___x_237_, v_prec_161_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprError_repr___boxed(lean_object* v_x_304_, lean_object* v_prec_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Http_Protocol_H1_instReprError_repr(v_x_304_, v_prec_305_);
lean_dec(v_prec_305_);
return v_res_306_;
}
}
uint8_t l_Std_Http_Protocol_H1_instBEqError_beq(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v_decide_313_; 
v___x_311_ = lean_obj_tag_nat(v_x_309_);
v___x_312_ = lean_obj_tag_nat(v_x_310_);
v_decide_313_ = lean_nat_dec_eq(v___x_311_, v___x_312_);
if (v_decide_313_ == 0)
{
return v_decide_313_;
}
else
{
if (lean_obj_tag(v_x_309_) == 11)
{
lean_object* v_message_314_; lean_object* v_message_315_; uint8_t v___x_316_; 
v_message_314_ = lean_ctor_get(v_x_309_, 0);
v_message_315_ = lean_ctor_get(v_x_310_, 0);
v___x_316_ = lean_string_dec_eq(v_message_314_, v_message_315_);
return v___x_316_;
}
else
{
return v_decide_313_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_instBEqError_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_309_ = stack[0].m_obj;
lean_object* v_x_310_ = stack[1].m_obj;
uint8_t v_res_317_;
v_res_317_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_x_309_, v_x_310_);
stack->m_num = v_res_317_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqError_beq___boxed(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_x_318_, v_x_319_);
lean_dec(v_x_319_);
lean_dec(v_x_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0(lean_object* v_x_336_){
_start:
{
switch(lean_obj_tag(v_x_336_))
{
case 0:
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0));
return v___x_337_;
}
case 1:
{
lean_object* v___x_338_; 
v___x_338_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1));
return v___x_338_;
}
case 2:
{
lean_object* v___x_339_; 
v___x_339_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2));
return v___x_339_;
}
case 3:
{
lean_object* v___x_340_; 
v___x_340_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3));
return v___x_340_;
}
case 4:
{
lean_object* v___x_341_; 
v___x_341_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4));
return v___x_341_;
}
case 5:
{
lean_object* v___x_342_; 
v___x_342_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5));
return v___x_342_;
}
case 6:
{
lean_object* v___x_343_; 
v___x_343_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6));
return v___x_343_;
}
case 7:
{
lean_object* v___x_344_; 
v___x_344_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7));
return v___x_344_;
}
case 8:
{
lean_object* v___x_345_; 
v___x_345_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8));
return v___x_345_;
}
case 9:
{
lean_object* v___x_346_; 
v___x_346_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9));
return v___x_346_;
}
case 10:
{
lean_object* v___x_347_; 
v___x_347_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10));
return v___x_347_;
}
default: 
{
lean_object* v_message_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_message_348_ = lean_ctor_get(v_x_336_, 0);
v___x_349_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11));
v___x_350_ = lean_string_append(v___x_349_, v_message_348_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed(lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_Http_Protocol_H1_instToStringError___lam__0(v_x_351_);
lean_dec(v_x_351_);
return v_res_352_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
