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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedTransferCoding_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedTransferCoding_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedMethod_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedMethod_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Std.Http.Protocol.H1.Error.unsupportedMethod"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__10_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__11_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Std.Http.Protocol.H1.Error.unsupportedTransferCoding"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__12_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__13_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Std.Http.Protocol.H1.Error.unsupportedVersion"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__14_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__15 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__15_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.Http.Protocol.H1.Error.uriTooLong"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__16 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__16_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__17_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Std.Http.Protocol.H1.Error.entityTooLarge"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__18_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__19 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__19_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Http.Protocol.H1.Error.timeout"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__20_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__21 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__21_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Http.Protocol.H1.Error.invalidHeader"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__22 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__22_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__22_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__23 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__23_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Std.Http.Protocol.H1.Error.invalidStatusLine"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__24 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__24_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__25 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__25_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__26;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__27;
static const lean_string_object l_Std_Http_Protocol_H1_instReprError_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Std.Http.Protocol.H1.Error.other"};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__28 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__28_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__28_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__29 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__29_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprError_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__29_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_instReprError_repr___closed__30 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprError_repr___closed__30_value;
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
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Unsupported transfer coding"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unsupported method"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Invalid chunk"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Connection closed"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Bad message"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Too many headers"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Headers too large"};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__12_value;
static const lean_string_object l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Other error: "};
static const lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__13_value;
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
if (lean_obj_tag(v_t_5_) == 13)
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedTransferCoding_elim___redArg(lean_object* v_t_69_, lean_object* v_unsupportedTransferCoding_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_69_, v_unsupportedTransferCoding_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedTransferCoding_elim(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_unsupportedTransferCoding_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_73_, v_unsupportedTransferCoding_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedMethod_elim___redArg(lean_object* v_t_77_, lean_object* v_unsupportedMethod_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_77_, v_unsupportedMethod_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_unsupportedMethod_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_unsupportedMethod_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_81_, v_unsupportedMethod_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidChunk_elim___redArg(lean_object* v_t_85_, lean_object* v_invalidChunk_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_85_, v_invalidChunk_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_invalidChunk_elim(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_invalidChunk_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_89_, v_invalidChunk_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_connectionClosed_elim___redArg(lean_object* v_t_93_, lean_object* v_connectionClosed_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_93_, v_connectionClosed_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_connectionClosed_elim(lean_object* v_motive_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_connectionClosed_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_97_, v_connectionClosed_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_badMessage_elim___redArg(lean_object* v_t_101_, lean_object* v_badMessage_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_101_, v_badMessage_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_badMessage_elim(lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_badMessage_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_105_, v_badMessage_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim___redArg(lean_object* v_t_109_, lean_object* v_tooManyHeaders_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_109_, v_tooManyHeaders_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_tooManyHeaders_elim(lean_object* v_motive_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_tooManyHeaders_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_113_, v_tooManyHeaders_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_headersTooLarge_elim___redArg(lean_object* v_t_117_, lean_object* v_headersTooLarge_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_117_, v_headersTooLarge_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_headersTooLarge_elim(lean_object* v_motive_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_headersTooLarge_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_121_, v_headersTooLarge_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_other_elim___redArg(lean_object* v_t_125_, lean_object* v_other_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_125_, v_other_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Error_other_elim(lean_object* v_motive_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_other_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Http_Protocol_H1_Error_ctorElim___redArg(v_t_129_, v_other_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(2u);
v___x_173_ = lean_nat_to_int(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_to_int(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprError_repr(lean_object* v_x_182_, lean_object* v_prec_183_){
_start:
{
lean_object* v___y_185_; lean_object* v___y_192_; lean_object* v___y_199_; lean_object* v___y_206_; lean_object* v___y_213_; lean_object* v___y_220_; lean_object* v___y_227_; lean_object* v___y_234_; lean_object* v___y_241_; lean_object* v___y_248_; lean_object* v___y_255_; lean_object* v___y_262_; lean_object* v___y_269_; 
switch(lean_obj_tag(v_x_182_))
{
case 0:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1024u);
v___x_276_ = lean_nat_dec_le(v___x_275_, v_prec_183_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_269_ = v___x_277_;
goto v___jp_268_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_269_ = v___x_278_;
goto v___jp_268_;
}
}
case 1:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1024u);
v___x_280_ = lean_nat_dec_le(v___x_279_, v_prec_183_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_262_ = v___x_281_;
goto v___jp_261_;
}
else
{
lean_object* v___x_282_; 
v___x_282_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_262_ = v___x_282_;
goto v___jp_261_;
}
}
case 2:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(1024u);
v___x_284_ = lean_nat_dec_le(v___x_283_, v_prec_183_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_255_ = v___x_285_;
goto v___jp_254_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_255_ = v___x_286_;
goto v___jp_254_;
}
}
case 3:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1024u);
v___x_288_ = lean_nat_dec_le(v___x_287_, v_prec_183_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_248_ = v___x_289_;
goto v___jp_247_;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_248_ = v___x_290_;
goto v___jp_247_;
}
}
case 4:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1024u);
v___x_292_ = lean_nat_dec_le(v___x_291_, v_prec_183_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_241_ = v___x_293_;
goto v___jp_240_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_241_ = v___x_294_;
goto v___jp_240_;
}
}
case 5:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1024u);
v___x_296_ = lean_nat_dec_le(v___x_295_, v_prec_183_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_234_ = v___x_297_;
goto v___jp_233_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_234_ = v___x_298_;
goto v___jp_233_;
}
}
case 6:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1024u);
v___x_300_ = lean_nat_dec_le(v___x_299_, v_prec_183_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_227_ = v___x_301_;
goto v___jp_226_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_227_ = v___x_302_;
goto v___jp_226_;
}
}
case 7:
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1024u);
v___x_304_ = lean_nat_dec_le(v___x_303_, v_prec_183_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_220_ = v___x_305_;
goto v___jp_219_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_220_ = v___x_306_;
goto v___jp_219_;
}
}
case 8:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1024u);
v___x_308_ = lean_nat_dec_le(v___x_307_, v_prec_183_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_213_ = v___x_309_;
goto v___jp_212_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_213_ = v___x_310_;
goto v___jp_212_;
}
}
case 9:
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(1024u);
v___x_312_ = lean_nat_dec_le(v___x_311_, v_prec_183_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_206_ = v___x_313_;
goto v___jp_205_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_206_ = v___x_314_;
goto v___jp_205_;
}
}
case 10:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1024u);
v___x_316_ = lean_nat_dec_le(v___x_315_, v_prec_183_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_199_ = v___x_317_;
goto v___jp_198_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_199_ = v___x_318_;
goto v___jp_198_;
}
}
case 11:
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1024u);
v___x_320_ = lean_nat_dec_le(v___x_319_, v_prec_183_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_192_ = v___x_321_;
goto v___jp_191_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_192_ = v___x_322_;
goto v___jp_191_;
}
}
case 12:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(1024u);
v___x_324_ = lean_nat_dec_le(v___x_323_, v_prec_183_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_185_ = v___x_325_;
goto v___jp_184_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_185_ = v___x_326_;
goto v___jp_184_;
}
}
default: 
{
lean_object* v_message_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_347_; 
v_message_327_ = lean_ctor_get(v_x_182_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_182_);
if (v_isSharedCheck_347_ == 0)
{
v___x_329_ = v_x_182_;
v_isShared_330_ = v_isSharedCheck_347_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_message_327_);
lean_dec(v_x_182_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_347_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___y_332_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1024u);
v___x_344_ = lean_nat_dec_le(v___x_343_, v_prec_183_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__26, &l_Std_Http_Protocol_H1_instReprError_repr___closed__26_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__26);
v___y_332_ = v___x_345_;
goto v___jp_331_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprError_repr___closed__27, &l_Std_Http_Protocol_H1_instReprError_repr___closed__27_once, _init_l_Std_Http_Protocol_H1_instReprError_repr___closed__27);
v___y_332_ = v___x_346_;
goto v___jp_331_;
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_333_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__30));
v___x_334_ = l_String_quote(v_message_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 3);
lean_ctor_set(v___x_329_, 0, v___x_334_);
v___x_336_ = v___x_329_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_342_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_333_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_inc(v___y_332_);
v___x_338_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_338_, 0, v___y_332_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = 0;
v___x_340_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*1, v___x_339_);
v___x_341_ = l_Repr_addAppParen(v___x_340_, v_prec_183_);
return v___x_341_;
}
}
}
}
}
v___jp_184_:
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_186_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__1));
lean_inc(v___y_185_);
v___x_187_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_187_, 0, v___y_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = 0;
v___x_189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_188_);
v___x_190_ = l_Repr_addAppParen(v___x_189_, v_prec_183_);
return v___x_190_;
}
v___jp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_193_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__3));
lean_inc(v___y_192_);
v___x_194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_194_, 0, v___y_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = 0;
v___x_196_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*1, v___x_195_);
v___x_197_ = l_Repr_addAppParen(v___x_196_, v_prec_183_);
return v___x_197_;
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_200_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__5));
lean_inc(v___y_199_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___y_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = 0;
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_202_);
v___x_204_ = l_Repr_addAppParen(v___x_203_, v_prec_183_);
return v___x_204_;
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_207_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__7));
lean_inc(v___y_206_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_183_);
return v___x_211_;
}
v___jp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_214_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__9));
lean_inc(v___y_213_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v___y_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = 0;
v___x_217_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*1, v___x_216_);
v___x_218_ = l_Repr_addAppParen(v___x_217_, v_prec_183_);
return v___x_218_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_221_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__11));
lean_inc(v___y_220_);
v___x_222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_222_, 0, v___y_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_223_);
v___x_225_ = l_Repr_addAppParen(v___x_224_, v_prec_183_);
return v___x_225_;
}
v___jp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_228_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__13));
lean_inc(v___y_227_);
v___x_229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_229_, 0, v___y_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_230_);
v___x_232_ = l_Repr_addAppParen(v___x_231_, v_prec_183_);
return v___x_232_;
}
v___jp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_235_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__15));
lean_inc(v___y_234_);
v___x_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_236_, 0, v___y_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = 0;
v___x_238_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*1, v___x_237_);
v___x_239_ = l_Repr_addAppParen(v___x_238_, v_prec_183_);
return v___x_239_;
}
v___jp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_242_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__17));
lean_inc(v___y_241_);
v___x_243_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_243_, 0, v___y_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = 0;
v___x_245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_244_);
v___x_246_ = l_Repr_addAppParen(v___x_245_, v_prec_183_);
return v___x_246_;
}
v___jp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_249_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__19));
lean_inc(v___y_248_);
v___x_250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_250_, 0, v___y_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = 0;
v___x_252_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*1, v___x_251_);
v___x_253_ = l_Repr_addAppParen(v___x_252_, v_prec_183_);
return v___x_253_;
}
v___jp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_256_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__21));
lean_inc(v___y_255_);
v___x_257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_257_, 0, v___y_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = 0;
v___x_259_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*1, v___x_258_);
v___x_260_ = l_Repr_addAppParen(v___x_259_, v_prec_183_);
return v___x_260_;
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__23));
lean_inc(v___y_262_);
v___x_264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_264_, 0, v___y_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v_prec_183_);
return v___x_267_;
}
v___jp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_270_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprError_repr___closed__25));
lean_inc(v___y_269_);
v___x_271_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_271_, 0, v___y_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = 0;
v___x_273_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___x_272_);
v___x_274_ = l_Repr_addAppParen(v___x_273_, v_prec_183_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprError_repr___boxed(lean_object* v_x_348_, lean_object* v_prec_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Http_Protocol_H1_instReprError_repr(v_x_348_, v_prec_349_);
lean_dec(v_prec_349_);
return v_res_350_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instBEqError_beq(lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v_decide_357_; 
v___x_355_ = lean_obj_tag_nat(v_x_353_);
v___x_356_ = lean_obj_tag_nat(v_x_354_);
v_decide_357_ = lean_nat_dec_eq(v___x_355_, v___x_356_);
if (v_decide_357_ == 0)
{
return v_decide_357_;
}
else
{
if (lean_obj_tag(v_x_353_) == 13)
{
lean_object* v_message_358_; lean_object* v_message_359_; uint8_t v___x_360_; 
v_message_358_ = lean_ctor_get(v_x_353_, 0);
v_message_359_ = lean_ctor_get(v_x_354_, 0);
v___x_360_ = lean_string_dec_eq(v_message_358_, v_message_359_);
return v___x_360_;
}
else
{
return v_decide_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instBEqError_beq___boxed(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_x_361_, v_x_362_);
lean_dec(v_x_362_);
lean_dec(v_x_361_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0(lean_object* v_x_381_){
_start:
{
switch(lean_obj_tag(v_x_381_))
{
case 0:
{
lean_object* v___x_382_; 
v___x_382_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__0));
return v___x_382_;
}
case 1:
{
lean_object* v___x_383_; 
v___x_383_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__1));
return v___x_383_;
}
case 2:
{
lean_object* v___x_384_; 
v___x_384_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__2));
return v___x_384_;
}
case 3:
{
lean_object* v___x_385_; 
v___x_385_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__3));
return v___x_385_;
}
case 4:
{
lean_object* v___x_386_; 
v___x_386_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__4));
return v___x_386_;
}
case 5:
{
lean_object* v___x_387_; 
v___x_387_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__5));
return v___x_387_;
}
case 6:
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__6));
return v___x_388_;
}
case 7:
{
lean_object* v___x_389_; 
v___x_389_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__7));
return v___x_389_;
}
case 8:
{
lean_object* v___x_390_; 
v___x_390_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__8));
return v___x_390_;
}
case 9:
{
lean_object* v___x_391_; 
v___x_391_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__9));
return v___x_391_;
}
case 10:
{
lean_object* v___x_392_; 
v___x_392_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__10));
return v___x_392_;
}
case 11:
{
lean_object* v___x_393_; 
v___x_393_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__11));
return v___x_393_;
}
case 12:
{
lean_object* v___x_394_; 
v___x_394_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__12));
return v___x_394_;
}
default: 
{
lean_object* v_message_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_message_395_ = lean_ctor_get(v_x_381_, 0);
v___x_396_ = ((lean_object*)(l_Std_Http_Protocol_H1_instToStringError___lam__0___closed__13));
v___x_397_ = lean_string_append(v___x_396_, v_message_395_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instToStringError___lam__0___boxed(lean_object* v_x_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_Http_Protocol_H1_instToStringError___lam__0(v_x_398_);
lean_dec(v_x_398_);
return v_res_399_;
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
