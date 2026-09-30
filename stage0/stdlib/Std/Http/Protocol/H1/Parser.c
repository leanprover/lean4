// Lean compiler output
// Module: Std.Http.Protocol.H1.Parser
// Imports: public import Std.Internal.Parsec public import Std.Http.Data public import Std.Internal.Parsec.ByteArray public import Std.Http.Protocol.H1.Config
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* lean_string_data(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x3f(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object*, lean_object*);
lean_object* l_Std_Http_Version_ofNumber_x3f(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of items"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "too many items: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " > "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected value but got none"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__1_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "too many leading empty lines"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '32'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid space sequence"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid hex digit "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expected hex digit"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "chunk size too large"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HTTP/"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '46'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__4_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unrecognized method"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "uri too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__1_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(128) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__0_value)} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unsupported HTTP version"};
static const lean_object* l_Std_Http_Protocol_H1_parseRequestLine___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_parseRequestLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_parseRequestLine___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_parseRequestLine___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '58'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_parseSingleHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_parseSingleHeader___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_parseSingleHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_parseSingleHeader___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '92'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid quoted-pair byte: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "quoted-string too long"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid qdtext byte: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '34'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid extension value"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '61'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__2_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid extension name"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__4_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '59'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__6_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "content-length"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "transfer-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "connection"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expect"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "te"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "authorization"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "max-forwards"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cache-control"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "content-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "upgrade"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trailer"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11_value;
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "forbidden trailer field: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid status code"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint8_t v___y_4_; uint32_t v___x_9_; uint8_t v___x_10_; 
v___x_2_ = lean_uint8_to_uint32(v_c_1_);
v___x_9_ = 33;
v___x_10_ = lean_uint32_dec_le(v___x_9_, v___x_2_);
if (v___x_10_ == 0)
{
v___y_4_ = v___x_10_;
goto v___jp_3_;
}
else
{
uint32_t v___x_11_; uint8_t v___x_12_; 
v___x_11_ = 126;
v___x_12_ = lean_uint32_dec_le(v___x_2_, v___x_11_);
v___y_4_ = v___x_12_;
goto v___jp_3_;
}
v___jp_3_:
{
if (v___y_4_ == 0)
{
uint32_t v___x_5_; uint8_t v___x_6_; 
v___x_5_ = 32;
v___x_6_ = lean_uint32_dec_eq(v___x_2_, v___x_5_);
if (v___x_6_ == 0)
{
uint32_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = 9;
v___x_8_ = lean_uint32_dec_eq(v___x_2_, v___x_7_);
return v___x_8_;
}
else
{
return v___x_6_;
}
}
else
{
return v___y_4_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object* v_c_13_){
_start:
{
uint8_t v_c_boxed_14_; uint8_t v_res_15_; lean_object* v_r_16_; 
v_c_boxed_14_ = lean_unbox(v_c_13_);
v_res_15_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(v_c_boxed_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t v_c_17_){
_start:
{
uint32_t v___x_18_; uint8_t v___y_20_; uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_18_ = lean_uint8_to_uint32(v_c_17_);
v___x_25_ = 9;
v___x_26_ = lean_uint32_dec_eq(v___x_18_, v___x_25_);
if (v___x_26_ == 0)
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 32;
v___x_28_ = lean_uint32_dec_eq(v___x_18_, v___x_27_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 33;
v___x_30_ = lean_uint32_dec_eq(v___x_18_, v___x_29_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 35;
v___x_32_ = lean_uint32_dec_le(v___x_31_, v___x_18_);
if (v___x_32_ == 0)
{
v___y_20_ = v___x_32_;
goto v___jp_19_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 91;
v___x_34_ = lean_uint32_dec_le(v___x_18_, v___x_33_);
v___y_20_ = v___x_34_;
goto v___jp_19_;
}
}
else
{
return v___x_30_;
}
}
else
{
return v___x_28_;
}
}
else
{
return v___x_26_;
}
v___jp_19_:
{
if (v___y_20_ == 0)
{
uint32_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 93;
v___x_22_ = lean_uint32_dec_le(v___x_21_, v___x_18_);
if (v___x_22_ == 0)
{
return v___x_22_;
}
else
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 126;
v___x_24_ = lean_uint32_dec_le(v___x_18_, v___x_23_);
return v___x_24_;
}
}
else
{
return v___y_20_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText___boxed(lean_object* v_c_35_){
_start:
{
uint8_t v_c_boxed_36_; uint8_t v_res_37_; lean_object* v_r_38_; 
v_c_boxed_36_ = lean_unbox(v_c_35_);
v_res_37_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(v_c_boxed_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t v_c_39_){
_start:
{
uint32_t v___x_40_; uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_40_ = lean_uint8_to_uint32(v_c_39_);
v___x_41_ = 32;
v___x_42_ = lean_uint32_dec_eq(v___x_40_, v___x_41_);
if (v___x_42_ == 0)
{
uint32_t v___x_43_; uint8_t v___x_44_; 
v___x_43_ = 9;
v___x_44_ = lean_uint32_dec_eq(v___x_40_, v___x_43_);
return v___x_44_;
}
else
{
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object* v_c_45_){
_start:
{
uint8_t v_c_boxed_46_; uint8_t v_res_47_; lean_object* v_r_48_; 
v_c_boxed_46_ = lean_unbox(v_c_45_);
v_res_47_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(v_c_boxed_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object* v_parser_54_, lean_object* v_maxCount_55_, lean_object* v_acc_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_pos_59_; lean_object* v_err_60_; lean_object* v___x_75_; 
lean_inc_ref(v_parser_54_);
lean_inc_ref(v_a_57_);
v___x_75_ = lean_apply_1(v_parser_54_, v_a_57_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_res_76_; 
v_res_76_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_res_76_);
if (lean_obj_tag(v_res_76_) == 0)
{
lean_object* v___x_77_; 
lean_dec_ref_known(v___x_75_, 2);
lean_dec(v_maxCount_55_);
lean_dec_ref(v_parser_54_);
v___x_77_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1));
lean_inc_ref(v_a_57_);
v_pos_59_ = v_a_57_;
v_err_60_ = v___x_77_;
goto v___jp_58_;
}
else
{
lean_object* v_pos_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_104_; 
lean_dec_ref(v_a_57_);
v_pos_78_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_75_, 1);
lean_dec(v_unused_105_);
v___x_80_ = v___x_75_;
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_pos_78_);
lean_dec(v___x_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_val_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_103_; 
v_val_82_ = lean_ctor_get(v_res_76_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_res_76_);
if (v_isSharedCheck_103_ == 0)
{
v___x_84_ = v_res_76_;
v_isShared_85_ = v_isSharedCheck_103_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_val_82_);
lean_dec(v_res_76_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_103_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_86_ = lean_array_push(v_acc_56_, v_val_82_);
v___x_87_ = lean_array_get_size(v___x_86_);
v___x_88_ = lean_nat_dec_lt(v_maxCount_55_, v___x_87_);
if (v___x_88_ == 0)
{
lean_del_object(v___x_84_);
lean_del_object(v___x_80_);
v_acc_56_ = v___x_86_;
v_a_57_ = v_pos_78_;
goto _start;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec_ref(v___x_86_);
lean_dec_ref(v_parser_54_);
v___x_90_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2));
v___x_91_ = l_Nat_reprFast(v___x_87_);
v___x_92_ = lean_string_append(v___x_90_, v___x_91_);
lean_dec_ref(v___x_91_);
v___x_93_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3));
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
v___x_95_ = l_Nat_reprFast(v_maxCount_55_);
v___x_96_ = lean_string_append(v___x_94_, v___x_95_);
lean_dec_ref(v___x_95_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_96_);
v___x_98_ = v___x_84_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_102_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_100_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 1);
lean_ctor_set(v___x_80_, 1, v___x_98_);
v___x_100_ = v___x_80_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_pos_78_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
}
}
else
{
lean_object* v_err_106_; 
lean_dec(v_maxCount_55_);
lean_dec_ref(v_parser_54_);
v_err_106_ = lean_ctor_get(v___x_75_, 1);
lean_inc(v_err_106_);
lean_dec_ref_known(v___x_75_, 2);
lean_inc_ref(v_a_57_);
v_pos_59_ = v_a_57_;
v_err_60_ = v_err_106_;
goto v___jp_58_;
}
v___jp_58_:
{
lean_object* v_idx_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_73_; 
v_idx_61_ = lean_ctor_get(v_a_57_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_a_57_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; 
v_unused_74_ = lean_ctor_get(v_a_57_, 0);
lean_dec(v_unused_74_);
v___x_63_ = v_a_57_;
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_idx_61_);
lean_dec(v_a_57_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v_idx_65_; uint8_t v___x_66_; 
v_idx_65_ = lean_ctor_get(v_pos_59_, 1);
v___x_66_ = lean_nat_dec_eq(v_idx_61_, v_idx_65_);
lean_dec(v_idx_61_);
if (v___x_66_ == 0)
{
lean_object* v___x_68_; 
lean_dec_ref(v_acc_56_);
if (v_isShared_64_ == 0)
{
lean_ctor_set_tag(v___x_63_, 1);
lean_ctor_set(v___x_63_, 1, v_err_60_);
lean_ctor_set(v___x_63_, 0, v_pos_59_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_pos_59_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_err_60_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
else
{
lean_object* v___x_71_; 
lean_dec(v_err_60_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v_acc_56_);
lean_ctor_set(v___x_63_, 0, v_pos_59_);
v___x_71_ = v___x_63_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_pos_59_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_acc_56_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object* v_00_u03b1_107_, lean_object* v_parser_108_, lean_object* v_maxCount_109_, lean_object* v_acc_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_108_, v_maxCount_109_, v_acc_110_, v_a_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object* v_parser_115_, lean_object* v_maxCount_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0));
v___x_119_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_115_, v_maxCount_116_, v___x_118_, v_a_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object* v_00_u03b1_120_, lean_object* v_parser_121_, lean_object* v_maxCount_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v_parser_121_, v_maxCount_122_, v_a_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object* v_x_128_, lean_object* v_a_129_){
_start:
{
if (lean_obj_tag(v_x_128_) == 1)
{
lean_object* v_val_130_; lean_object* v___x_131_; 
v_val_130_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_val_130_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_a_129_);
lean_ctor_set(v___x_131_, 1, v_val_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1));
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v_a_129_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object* v_x_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_134_, v_a_135_);
lean_dec(v_x_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object* v_00_u03b1_137_, lean_object* v_x_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_138_, v_a_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object* v_00_u03b1_141_, lean_object* v_x_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(v_00_u03b1_141_, v_x_142_, v_a_143_);
lean_dec(v_x_142_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t v_c_145_){
_start:
{
uint32_t v___x_146_; uint8_t v___y_148_; uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_146_ = lean_uint8_to_uint32(v_c_145_);
v___x_158_ = 33;
v___x_159_ = lean_uint32_dec_eq(v___x_146_, v___x_158_);
if (v___x_159_ == 0)
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 35;
v___x_161_ = lean_uint32_dec_eq(v___x_146_, v___x_160_);
if (v___x_161_ == 0)
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 36;
v___x_163_ = lean_uint32_dec_eq(v___x_146_, v___x_162_);
if (v___x_163_ == 0)
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 37;
v___x_165_ = lean_uint32_dec_eq(v___x_146_, v___x_164_);
if (v___x_165_ == 0)
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 38;
v___x_167_ = lean_uint32_dec_eq(v___x_146_, v___x_166_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 39;
v___x_169_ = lean_uint32_dec_eq(v___x_146_, v___x_168_);
if (v___x_169_ == 0)
{
uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 42;
v___x_171_ = lean_uint32_dec_eq(v___x_146_, v___x_170_);
if (v___x_171_ == 0)
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 43;
v___x_173_ = lean_uint32_dec_eq(v___x_146_, v___x_172_);
if (v___x_173_ == 0)
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 45;
v___x_175_ = lean_uint32_dec_eq(v___x_146_, v___x_174_);
if (v___x_175_ == 0)
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 46;
v___x_177_ = lean_uint32_dec_eq(v___x_146_, v___x_176_);
if (v___x_177_ == 0)
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 94;
v___x_179_ = lean_uint32_dec_eq(v___x_146_, v___x_178_);
if (v___x_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 95;
v___x_181_ = lean_uint32_dec_eq(v___x_146_, v___x_180_);
if (v___x_181_ == 0)
{
uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = 96;
v___x_183_ = lean_uint32_dec_eq(v___x_146_, v___x_182_);
if (v___x_183_ == 0)
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 124;
v___x_185_ = lean_uint32_dec_eq(v___x_146_, v___x_184_);
if (v___x_185_ == 0)
{
uint32_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = 126;
v___x_187_ = lean_uint32_dec_eq(v___x_146_, v___x_186_);
if (v___x_187_ == 0)
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 48;
v___x_189_ = lean_uint32_dec_le(v___x_188_, v___x_146_);
if (v___x_189_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = 57;
v___x_191_ = lean_uint32_dec_le(v___x_146_, v___x_190_);
if (v___x_191_ == 0)
{
goto v___jp_153_;
}
else
{
return v___x_191_;
}
}
}
else
{
return v___x_187_;
}
}
else
{
return v___x_185_;
}
}
else
{
return v___x_183_;
}
}
else
{
return v___x_181_;
}
}
else
{
return v___x_179_;
}
}
else
{
return v___x_177_;
}
}
else
{
return v___x_175_;
}
}
else
{
return v___x_173_;
}
}
else
{
return v___x_171_;
}
}
else
{
return v___x_169_;
}
}
else
{
return v___x_167_;
}
}
else
{
return v___x_165_;
}
}
else
{
return v___x_163_;
}
}
else
{
return v___x_161_;
}
}
else
{
return v___x_159_;
}
v___jp_147_:
{
if (v___y_148_ == 0)
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 97;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v___x_146_);
if (v___x_150_ == 0)
{
return v___x_150_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 122;
v___x_152_ = lean_uint32_dec_le(v___x_146_, v___x_151_);
return v___x_152_;
}
}
else
{
return v___y_148_;
}
}
v___jp_153_:
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 65;
v___x_155_ = lean_uint32_dec_le(v___x_154_, v___x_146_);
if (v___x_155_ == 0)
{
v___y_148_ = v___x_155_;
goto v___jp_147_;
}
else
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 90;
v___x_157_ = lean_uint32_dec_le(v___x_146_, v___x_156_);
v___y_148_ = v___x_157_;
goto v___jp_147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object* v_c_192_){
_start:
{
uint8_t v_c_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_c_boxed_193_ = lean_unbox(v_c_192_);
v_res_194_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_boxed_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object* v_limit_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_snd_205_; lean_object* v_snd_206_; uint8_t v___x_207_; 
v___f_202_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_203_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_201_);
v___x_204_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_202_, v_limit_200_, v___x_203_, v_a_201_);
v_snd_205_ = lean_ctor_get(v___x_204_, 1);
lean_inc(v_snd_205_);
v_snd_206_ = lean_ctor_get(v_snd_205_, 1);
v___x_207_ = lean_unbox(v_snd_206_);
if (v___x_207_ == 0)
{
lean_object* v_fst_208_; lean_object* v_fst_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_237_; 
v_fst_208_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_fst_208_);
lean_dec_ref(v___x_204_);
v_fst_209_ = lean_ctor_get(v_snd_205_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_snd_205_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_snd_205_, 1);
lean_dec(v_unused_238_);
v___x_211_ = v_snd_205_;
v_isShared_212_ = v_isSharedCheck_237_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_fst_209_);
lean_dec(v_snd_205_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_237_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
uint8_t v___x_213_; 
v___x_213_ = lean_nat_dec_eq(v_fst_208_, v___x_203_);
if (v___x_213_ == 0)
{
lean_object* v_array_214_; lean_object* v_idx_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_232_; 
lean_del_object(v___x_211_);
v_array_214_ = lean_ctor_get(v_a_201_, 0);
v_idx_215_ = lean_ctor_get(v_a_201_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_a_201_);
if (v_isSharedCheck_232_ == 0)
{
v___x_217_ = v_a_201_;
v_isShared_218_ = v_isSharedCheck_232_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_idx_215_);
lean_inc(v_array_214_);
lean_dec(v_a_201_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_232_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_lower_220_; lean_object* v_upper_221_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___y_229_; uint8_t v___x_231_; 
v___x_226_ = lean_nat_add(v_idx_215_, v_fst_208_);
lean_dec(v_fst_208_);
v___x_227_ = lean_byte_array_size(v_array_214_);
v___x_231_ = lean_nat_dec_le(v_idx_215_, v___x_203_);
if (v___x_231_ == 0)
{
v___y_229_ = v_idx_215_;
goto v___jp_228_;
}
else
{
lean_dec(v_idx_215_);
v___y_229_ = v___x_203_;
goto v___jp_228_;
}
v___jp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = l_ByteArray_toByteSlice(v_array_214_, v_lower_220_, v_upper_221_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_222_);
lean_ctor_set(v___x_217_, 0, v_fst_209_);
v___x_224_ = v___x_217_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_fst_209_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
v___jp_228_:
{
uint8_t v___x_230_; 
v___x_230_ = lean_nat_dec_le(v___x_226_, v___x_227_);
if (v___x_230_ == 0)
{
lean_dec(v___x_226_);
v_lower_220_ = v___y_229_;
v_upper_221_ = v___x_227_;
goto v___jp_219_;
}
else
{
v_lower_220_ = v___y_229_;
v_upper_221_ = v___x_226_;
goto v___jp_219_;
}
}
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_235_; 
lean_dec(v_fst_209_);
lean_dec(v_fst_208_);
v___x_233_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_212_ == 0)
{
lean_ctor_set_tag(v___x_211_, 1);
lean_ctor_set(v___x_211_, 1, v___x_233_);
lean_ctor_set(v___x_211_, 0, v_a_201_);
v___x_235_ = v___x_211_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_201_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v_fst_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_a_201_);
v_fst_239_ = lean_ctor_get(v_snd_205_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_snd_205_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v_snd_205_, 1);
lean_dec(v_unused_248_);
v___x_241_ = v_snd_205_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_fst_239_);
lean_dec(v_snd_205_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_box(0);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
lean_ctor_set(v___x_241_, 1, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object* v_limit_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(v_limit_249_, v_a_250_);
lean_dec(v_limit_249_);
return v_res_251_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0));
v___x_254_ = lean_string_to_utf8(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object* v_a_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_257_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_256_, v_a_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object* v_limits_261_, lean_object* v_a_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_array_264_; lean_object* v_idx_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_array_264_ = lean_ctor_get(v___y_263_, 0);
v_idx_265_ = lean_ctor_get(v___y_263_, 1);
v___x_266_ = lean_byte_array_size(v_array_264_);
v___x_267_ = lean_nat_dec_lt(v_idx_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___y_263_);
lean_ctor_set(v___x_268_, 1, v_a_262_);
return v___x_268_;
}
else
{
uint8_t v___x_269_; uint8_t v___x_270_; uint8_t v___x_271_; 
v___x_269_ = lean_byte_array_fget(v_array_264_, v_idx_265_);
v___x_270_ = 13;
v___x_271_ = lean_uint8_dec_eq(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_263_);
lean_ctor_set(v___x_272_, 1, v_a_262_);
return v___x_272_;
}
else
{
lean_object* v_maxLeadingEmptyLines_273_; uint8_t v___x_274_; 
v_maxLeadingEmptyLines_273_ = lean_ctor_get(v_limits_261_, 9);
v___x_274_ = lean_nat_dec_le(v_maxLeadingEmptyLines_273_, v_a_262_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_276_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_275_, v___y_263_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_pos_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_pos_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_pos_277_);
lean_dec_ref_known(v___x_276_, 2);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_a_262_, v___x_278_);
lean_dec(v_a_262_);
v_a_262_ = v___x_279_;
v___y_263_ = v_pos_277_;
goto _start;
}
else
{
lean_object* v_pos_281_; lean_object* v_err_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec(v_a_262_);
v_pos_281_ = lean_ctor_get(v___x_276_, 0);
v_err_282_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_276_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_err_282_);
lean_inc(v_pos_281_);
lean_dec(v___x_276_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_pos_281_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_err_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_a_262_);
v___x_290_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1));
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_263_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object* v_limits_292_, lean_object* v_a_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_292_, v_a_293_, v___y_294_);
lean_dec_ref(v_limits_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_count_298_; lean_object* v___x_299_; 
v_count_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_296_, v_count_298_, v_a_297_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_pos_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
v_pos_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_299_, 1);
lean_dec(v_unused_309_);
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_pos_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = lean_box(0);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_pos_300_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_object* v_pos_310_; lean_object* v_err_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_pos_310_ = lean_ctor_get(v___x_299_, 0);
v_err_311_ = lean_ctor_get(v___x_299_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_299_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_err_311_);
lean_inc(v_pos_310_);
lean_dec(v___x_299_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_pos_310_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_err_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object* v_limits_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_319_, v_a_320_);
lean_dec_ref(v_limits_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_322_, lean_object* v_inst_323_, lean_object* v_a_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_322_, v_a_324_, v___y_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_327_, lean_object* v_inst_328_, lean_object* v_a_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_327_, v_inst_328_, v_a_329_, v___y_330_);
lean_dec_ref(v_limits_327_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_335_){
_start:
{
lean_object* v_array_336_; lean_object* v_idx_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_array_336_ = lean_ctor_get(v_a_335_, 0);
v_idx_337_ = lean_ctor_get(v_a_335_, 1);
v___x_338_ = lean_byte_array_size(v_array_336_);
v___x_339_ = lean_nat_dec_lt(v_idx_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v_a_335_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
return v___x_341_;
}
else
{
uint8_t v___x_342_; uint8_t v_got_343_; uint8_t v___x_344_; 
v___x_342_ = 32;
v_got_343_ = lean_byte_array_fget(v_array_336_, v_idx_337_);
v___x_344_ = lean_uint8_dec_eq(v_got_343_, v___x_342_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_346_, 0, v_a_335_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
return v___x_346_;
}
else
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_357_; 
lean_inc(v_idx_337_);
lean_inc_ref(v_array_336_);
v_isSharedCheck_357_ = !lean_is_exclusive(v_a_335_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; lean_object* v_unused_359_; 
v_unused_358_ = lean_ctor_get(v_a_335_, 1);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_a_335_, 0);
lean_dec(v_unused_359_);
v___x_348_ = v_a_335_;
v_isShared_349_ = v_isSharedCheck_357_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_a_335_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_357_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_idx_337_, v___x_350_);
lean_dec(v_idx_337_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_351_);
v___x_353_ = v___x_348_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_array_336_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_356_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
return v___x_355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_pos_367_; lean_object* v_pos_371_; lean_object* v_maxSpaceSequence_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_snd_378_; lean_object* v_snd_379_; uint8_t v___x_380_; 
v_maxSpaceSequence_374_ = lean_ctor_get(v_limits_364_, 8);
v___x_375_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_375_, v_maxSpaceSequence_374_, v___x_376_, v_a_365_);
v_snd_378_ = lean_ctor_get(v___x_377_, 1);
lean_inc(v_snd_378_);
lean_dec_ref(v___x_377_);
v_snd_379_ = lean_ctor_get(v_snd_378_, 1);
v___x_380_ = lean_unbox(v_snd_379_);
if (v___x_380_ == 0)
{
lean_object* v_fst_381_; lean_object* v_array_382_; lean_object* v_idx_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_fst_381_ = lean_ctor_get(v_snd_378_, 0);
lean_inc(v_fst_381_);
lean_dec(v_snd_378_);
v_array_382_ = lean_ctor_get(v_fst_381_, 0);
v_idx_383_ = lean_ctor_get(v_fst_381_, 1);
v___x_384_ = lean_byte_array_size(v_array_382_);
v___x_385_ = lean_nat_dec_lt(v_idx_383_, v___x_384_);
if (v___x_385_ == 0)
{
v_pos_367_ = v_fst_381_;
goto v___jp_366_;
}
else
{
uint8_t v___x_386_; uint32_t v___x_387_; uint32_t v___x_388_; uint8_t v___x_389_; 
v___x_386_ = lean_byte_array_fget(v_array_382_, v_idx_383_);
v___x_387_ = lean_uint8_to_uint32(v___x_386_);
v___x_388_ = 32;
v___x_389_ = lean_uint32_dec_eq(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 9;
v___x_391_ = lean_uint32_dec_eq(v___x_387_, v___x_390_);
if (v___x_391_ == 0)
{
v_pos_367_ = v_fst_381_;
goto v___jp_366_;
}
else
{
v_pos_371_ = v_fst_381_;
goto v___jp_370_;
}
}
else
{
v_pos_371_ = v_fst_381_;
goto v___jp_370_;
}
}
}
else
{
lean_object* v_fst_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_fst_392_ = lean_ctor_get(v_snd_378_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_snd_378_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v_snd_378_, 1);
lean_dec(v_unused_401_);
v___x_394_ = v_snd_378_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_fst_392_);
lean_dec(v_snd_378_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = lean_box(0);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 1, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_fst_392_);
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
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_box(0);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_pos_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
v___jp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_373_, 0, v_pos_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_402_, v_a_403_);
lean_dec_ref(v_limits_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_406_){
_start:
{
lean_object* v_array_407_; lean_object* v_idx_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_array_407_ = lean_ctor_get(v_a_406_, 0);
v_idx_408_ = lean_ctor_get(v_a_406_, 1);
v___x_409_ = lean_byte_array_size(v_array_407_);
v___x_410_ = lean_nat_dec_lt(v_idx_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_box(0);
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v_a_406_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
return v___x_412_;
}
else
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_468_; 
lean_inc(v_idx_408_);
lean_inc_ref(v_array_407_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; 
v_unused_469_ = lean_ctor_get(v_a_406_, 1);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_a_406_, 0);
lean_dec(v_unused_470_);
v___x_414_ = v_a_406_;
v_isShared_415_ = v_isSharedCheck_468_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_a_406_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_468_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v_c_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_it_x27_420_; 
v_c_416_ = lean_byte_array_fget(v_array_407_, v_idx_408_);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_add(v_idx_408_, v___x_417_);
lean_dec(v_idx_408_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_418_);
v_it_x27_420_ = v___x_414_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_array_407_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_418_);
v_it_x27_420_ = v_reuseFailAlloc_467_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 48;
v___x_464_ = lean_uint8_dec_le(v___x_463_, v_c_416_);
if (v___x_464_ == 0)
{
goto v___jp_458_;
}
else
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = 57;
v___x_466_ = lean_uint8_dec_le(v_c_416_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_458_;
}
else
{
goto v___jp_438_;
}
}
v___jp_421_:
{
uint8_t v___x_422_; uint8_t v___x_423_; uint8_t v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_422_ = 97;
v___x_423_ = lean_uint8_sub(v_c_416_, v___x_422_);
v___x_424_ = 10;
v___x_425_ = lean_uint8_add(v___x_423_, v___x_424_);
v___x_426_ = lean_box(v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_it_x27_420_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
return v___x_427_;
}
v___jp_428_:
{
uint8_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 65;
v___x_430_ = lean_uint8_dec_le(v___x_429_, v_c_416_);
if (v___x_430_ == 0)
{
goto v___jp_421_;
}
else
{
uint8_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 70;
v___x_432_ = lean_uint8_dec_le(v_c_416_, v___x_431_);
if (v___x_432_ == 0)
{
goto v___jp_421_;
}
else
{
uint8_t v___x_433_; uint8_t v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_433_ = lean_uint8_sub(v_c_416_, v___x_429_);
v___x_434_ = 10;
v___x_435_ = lean_uint8_add(v___x_433_, v___x_434_);
v___x_436_ = lean_box(v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_it_x27_420_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
return v___x_437_;
}
}
}
v___jp_438_:
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 48;
v___x_440_ = lean_uint8_dec_le(v___x_439_, v_c_416_);
if (v___x_440_ == 0)
{
goto v___jp_428_;
}
else
{
uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 57;
v___x_442_ = lean_uint8_dec_le(v_c_416_, v___x_441_);
if (v___x_442_ == 0)
{
goto v___jp_428_;
}
else
{
uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_uint8_sub(v_c_416_, v___x_439_);
v___x_444_ = lean_box(v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_it_x27_420_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
return v___x_445_;
}
}
}
v___jp_446_:
{
lean_object* v___x_447_; uint32_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_447_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0));
v___x_448_ = lean_uint8_to_uint32(v_c_416_);
v___x_449_ = l_Char_quote(v___x_448_);
v___x_450_ = lean_string_append(v___x_447_, v___x_449_);
lean_dec_ref(v___x_449_);
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v_it_x27_420_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
return v___x_452_;
}
v___jp_453_:
{
uint8_t v___x_454_; uint8_t v___x_455_; 
v___x_454_ = 65;
v___x_455_ = lean_uint8_dec_le(v___x_454_, v_c_416_);
if (v___x_455_ == 0)
{
goto v___jp_446_;
}
else
{
uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = 70;
v___x_457_ = lean_uint8_dec_le(v_c_416_, v___x_456_);
if (v___x_457_ == 0)
{
goto v___jp_446_;
}
else
{
goto v___jp_438_;
}
}
}
v___jp_458_:
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 97;
v___x_460_ = lean_uint8_dec_le(v___x_459_, v_c_416_);
if (v___x_460_ == 0)
{
goto v___jp_453_;
}
else
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 102;
v___x_462_ = lean_uint8_dec_le(v_c_416_, v___x_461_);
if (v___x_462_ == 0)
{
goto v___jp_453_;
}
else
{
goto v___jp_438_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object* v_acc_477_, lean_object* v_count_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_pos_481_; lean_object* v_err_482_; lean_object* v___x_510_; 
lean_inc_ref(v_a_479_);
v___x_510_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_479_);
if (lean_obj_tag(v___x_510_) == 0)
{
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_pos_511_; lean_object* v_res_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v_a_479_);
v_pos_511_ = lean_ctor_get(v___x_510_, 0);
v_res_512_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_529_ == 0)
{
v___x_514_ = v___x_510_;
v_isShared_515_ = v_isSharedCheck_529_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_res_512_);
lean_inc(v_pos_511_);
lean_dec(v___x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_529_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_516_ = lean_unsigned_to_nat(16u);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_count_478_, v___x_517_);
lean_dec(v_count_478_);
v___x_519_ = lean_nat_dec_lt(v___x_516_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_del_object(v___x_514_);
v___x_520_ = lean_nat_mul(v_acc_477_, v___x_516_);
lean_dec(v_acc_477_);
v___x_521_ = lean_unbox(v_res_512_);
lean_dec(v_res_512_);
v___x_522_ = lean_uint8_to_nat(v___x_521_);
v___x_523_ = lean_nat_add(v___x_520_, v___x_522_);
lean_dec(v___x_520_);
v_acc_477_ = v___x_523_;
v_count_478_ = v___x_518_;
v_a_479_ = v_pos_511_;
goto _start;
}
else
{
lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec(v___x_518_);
lean_dec(v_res_512_);
lean_dec(v_acc_477_);
v___x_525_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_515_ == 0)
{
lean_ctor_set_tag(v___x_514_, 1);
lean_ctor_set(v___x_514_, 1, v___x_525_);
v___x_527_ = v___x_514_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_pos_511_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v_pos_530_; lean_object* v_err_531_; 
v_pos_530_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_pos_530_);
v_err_531_ = lean_ctor_get(v___x_510_, 1);
lean_inc(v_err_531_);
lean_dec_ref_known(v___x_510_, 2);
v_pos_481_ = v_pos_530_;
v_err_482_ = v_err_531_;
goto v___jp_480_;
}
}
else
{
lean_object* v_err_532_; 
v_err_532_ = lean_ctor_get(v___x_510_, 1);
lean_inc(v_err_532_);
lean_dec_ref_known(v___x_510_, 2);
lean_inc_ref(v_a_479_);
v_pos_481_ = v_a_479_;
v_err_482_ = v_err_532_;
goto v___jp_480_;
}
v___jp_480_:
{
lean_object* v_idx_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_508_; 
v_idx_483_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_a_479_, 0);
lean_dec(v_unused_509_);
v___x_485_ = v_a_479_;
v_isShared_486_ = v_isSharedCheck_508_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_idx_483_);
lean_dec(v_a_479_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_508_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_array_487_; lean_object* v_idx_488_; uint8_t v___x_489_; 
v_array_487_ = lean_ctor_get(v_pos_481_, 0);
v_idx_488_ = lean_ctor_get(v_pos_481_, 1);
v___x_489_ = lean_nat_dec_eq(v_idx_483_, v_idx_488_);
lean_dec(v_idx_483_);
if (v___x_489_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v_count_478_);
lean_dec(v_acc_477_);
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 1);
lean_ctor_set(v___x_485_, 1, v_err_482_);
lean_ctor_set(v___x_485_, 0, v_pos_481_);
v___x_491_ = v___x_485_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_pos_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_err_482_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
else
{
lean_object* v___x_493_; uint8_t v___x_494_; 
lean_dec(v_err_482_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_nat_dec_eq(v_count_478_, v___x_493_);
lean_dec(v_count_478_);
if (v___x_494_ == 0)
{
lean_object* v___x_496_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v_acc_477_);
lean_ctor_set(v___x_485_, 0, v_pos_481_);
v___x_496_ = v___x_485_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_pos_481_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_acc_477_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
else
{
lean_object* v___x_498_; uint8_t v___x_499_; 
lean_dec(v_acc_477_);
v___x_498_ = lean_byte_array_size(v_array_487_);
v___x_499_ = lean_nat_dec_lt(v_idx_488_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_box(0);
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 1);
lean_ctor_set(v___x_485_, 1, v___x_500_);
lean_ctor_set(v___x_485_, 0, v_pos_481_);
v___x_502_ = v___x_485_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_pos_481_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 1);
lean_ctor_set(v___x_485_, 1, v___x_504_);
lean_ctor_set(v___x_485_, 0, v_pos_481_);
v___x_506_ = v___x_485_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_pos_481_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_534_, v___x_534_, v_a_533_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_538_ = lean_string_to_utf8(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_547_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_546_, v_a_545_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_pos_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_619_; 
v_pos_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_547_, 1);
lean_dec(v_unused_620_);
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_619_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_pos_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_619_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_array_552_; lean_object* v_idx_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_array_552_ = lean_ctor_get(v_pos_548_, 0);
v_idx_553_ = lean_ctor_get(v_pos_548_, 1);
v___x_554_ = lean_byte_array_size(v_array_552_);
v___x_555_ = lean_nat_dec_lt(v_idx_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_box(0);
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 1);
lean_ctor_set(v___x_550_, 1, v___x_556_);
v___x_558_ = v___x_550_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_pos_548_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
else
{
uint8_t v_c_560_; lean_object* v___x_561_; lean_object* v___y_563_; lean_object* v___y_564_; uint8_t v___y_565_; lean_object* v___y_566_; uint8_t v___y_567_; uint8_t v___x_584_; uint8_t v___x_585_; uint8_t v___x_586_; uint8_t v___y_588_; 
v_c_560_ = lean_byte_array_fget(v_array_552_, v_idx_553_);
v___x_561_ = lean_unsigned_to_nat(48u);
v___x_584_ = 48;
v___x_585_ = lean_uint8_dec_le(v___x_584_, v_c_560_);
v___x_586_ = 57;
if (v___x_585_ == 0)
{
v___y_588_ = v___x_585_;
goto v___jp_587_;
}
else
{
uint8_t v___x_618_; 
v___x_618_ = lean_uint8_dec_le(v_c_560_, v___x_586_);
v___y_588_ = v___x_618_;
goto v___jp_587_;
}
v___jp_562_:
{
if (v___y_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v___y_563_);
lean_dec_ref(v_array_552_);
v___x_568_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 1);
lean_ctor_set(v___x_550_, 1, v___x_568_);
lean_ctor_set(v___x_550_, 0, v___y_564_);
v___x_570_ = v___x_550_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___y_564_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
uint32_t v___x_572_; lean_object* v___x_573_; lean_object* v_it_x27_574_; uint32_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec_ref(v___y_564_);
v___x_572_ = lean_uint8_to_uint32(v_c_560_);
v___x_573_ = lean_nat_add(v___y_563_, v___y_566_);
lean_dec(v___y_563_);
v_it_x27_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_574_, 0, v_array_552_);
lean_ctor_set(v_it_x27_574_, 1, v___x_573_);
v___x_575_ = lean_uint8_to_uint32(v___y_565_);
v___x_576_ = lean_uint32_to_nat(v___x_572_);
v___x_577_ = lean_nat_sub(v___x_576_, v___x_561_);
lean_dec(v___x_576_);
v___x_578_ = lean_uint32_to_nat(v___x_575_);
v___x_579_ = lean_nat_sub(v___x_578_, v___x_561_);
lean_dec(v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_577_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_580_);
lean_ctor_set(v___x_550_, 0, v_it_x27_574_);
v___x_582_ = v___x_550_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_it_x27_574_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
v___jp_587_:
{
if (v___y_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_del_object(v___x_550_);
v___x_589_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_590_, 0, v_pos_548_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
return v___x_590_;
}
else
{
lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_615_; 
lean_inc(v_idx_553_);
lean_inc_ref(v_array_552_);
v_isSharedCheck_615_ = !lean_is_exclusive(v_pos_548_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; lean_object* v_unused_617_; 
v_unused_616_ = lean_ctor_get(v_pos_548_, 1);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_pos_548_, 0);
lean_dec(v_unused_617_);
v___x_592_ = v_pos_548_;
v_isShared_593_ = v_isSharedCheck_615_;
goto v_resetjp_591_;
}
else
{
lean_dec(v_pos_548_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_615_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_it_x27_597_; 
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_add(v_idx_553_, v___x_594_);
lean_dec(v_idx_553_);
lean_inc(v___x_595_);
lean_inc_ref(v_array_552_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_595_);
v_it_x27_597_ = v___x_592_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_array_552_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_595_);
v_it_x27_597_ = v_reuseFailAlloc_614_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
uint8_t v___x_598_; 
v___x_598_ = lean_nat_dec_lt(v___x_595_, v___x_554_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v___x_595_);
lean_dec_ref(v_array_552_);
lean_del_object(v___x_550_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_600_, 0, v_it_x27_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
else
{
uint8_t v___x_601_; uint8_t v_got_602_; uint8_t v___x_603_; 
v___x_601_ = 46;
v_got_602_ = lean_byte_array_fget(v_array_552_, v___x_595_);
v___x_603_ = lean_uint8_dec_eq(v_got_602_, v___x_601_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v___x_595_);
lean_dec_ref(v_array_552_);
lean_del_object(v___x_550_);
v___x_604_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5));
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v_it_x27_597_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
lean_dec_ref(v_it_x27_597_);
v___x_606_ = lean_nat_add(v___x_595_, v___x_594_);
lean_dec(v___x_595_);
lean_inc(v___x_606_);
lean_inc_ref(v_array_552_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v_array_552_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_nat_dec_lt(v___x_606_, v___x_554_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v___x_606_);
lean_dec_ref(v_array_552_);
lean_del_object(v___x_550_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_607_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
return v___x_610_;
}
else
{
uint8_t v_c_611_; uint8_t v___x_612_; 
v_c_611_ = lean_byte_array_fget(v_array_552_, v___x_606_);
v___x_612_ = lean_uint8_dec_le(v___x_584_, v_c_611_);
if (v___x_612_ == 0)
{
v___y_563_ = v___x_606_;
v___y_564_ = v___x_607_;
v___y_565_ = v_c_611_;
v___y_566_ = v___x_594_;
v___y_567_ = v___x_612_;
goto v___jp_562_;
}
else
{
uint8_t v___x_613_; 
v___x_613_ = lean_uint8_dec_le(v_c_611_, v___x_586_);
v___y_563_ = v___x_606_;
v___y_564_ = v___x_607_;
v___y_565_ = v_c_611_;
v___y_566_ = v___x_594_;
v___y_567_ = v___x_613_;
goto v___jp_562_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_pos_621_; lean_object* v_err_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
v_pos_621_ = lean_ctor_get(v___x_547_, 0);
v_err_622_ = lean_ctor_get(v___x_547_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_547_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_err_622_);
lean_inc(v_pos_621_);
lean_dec(v___x_547_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_pos_621_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_err_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_630_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_res_632_; lean_object* v_pos_633_; lean_object* v_fst_634_; lean_object* v_snd_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_res_632_ = lean_ctor_get(v___x_631_, 1);
lean_inc(v_res_632_);
v_pos_633_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_pos_633_);
lean_dec_ref_known(v___x_631_, 2);
v_fst_634_ = lean_ctor_get(v_res_632_, 0);
lean_inc(v_fst_634_);
v_snd_635_ = lean_ctor_get(v_res_632_, 1);
lean_inc(v_snd_635_);
lean_dec(v_res_632_);
v___x_636_ = l_Std_Http_Version_ofNumber_x3f(v_fst_634_, v_snd_635_);
lean_dec(v_snd_635_);
lean_dec(v_fst_634_);
v___x_637_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_636_, v_pos_633_);
lean_dec(v___x_636_);
return v___x_637_;
}
else
{
lean_object* v_pos_638_; lean_object* v_err_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
v_pos_638_ = lean_ctor_get(v___x_631_, 0);
v_err_639_ = lean_ctor_get(v___x_631_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_631_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_err_639_);
lean_inc(v_pos_638_);
lean_dec(v___x_631_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_pos_638_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_err_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object* v_a_647_, lean_object* v_f_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_apply_1(v_a_647_, v___y_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_pos_651_; lean_object* v_res_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_pos_651_ = lean_ctor_get(v___x_650_, 0);
v_res_652_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_res_652_);
lean_inc(v_pos_651_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_apply_1(v_f_648_, v_res_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_pos_651_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_pos_661_; lean_object* v_err_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_f_648_);
v_pos_661_ = lean_ctor_get(v___x_650_, 0);
v_err_662_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_650_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_err_662_);
lean_inc(v_pos_661_);
lean_dec(v___x_650_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_pos_661_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_err_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v_00_u03b1_670_, lean_object* v_00_u03b2_671_, lean_object* v_a_672_, lean_object* v_f_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v_a_672_, v_f_673_, v___y_674_);
return v___x_675_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object* v_x_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = 9;
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object* v_x_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object* v_x_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = 32;
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object* v_x_683_){
_start:
{
uint8_t v_res_684_; lean_object* v_r_685_; 
v_res_684_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_683_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object* v_x_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = 28;
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object* v_x_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object* v_x_691_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = 1;
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object* v_x_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_693_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object* v_x_696_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = 5;
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object* v_x_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_698_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object* v_x_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = 4;
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_703_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object* v_x_706_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = 10;
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object* v_x_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_708_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object* v_x_711_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = 12;
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object* v_x_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_713_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object* v_x_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = 14;
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object* v_x_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(v_x_718_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object* v_x_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = 16;
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object* v_x_723_){
_start:
{
uint8_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_723_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object* v_x_726_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = 18;
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object* v_x_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_728_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object* v_x_731_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = 20;
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object* v_x_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object* v_x_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = 23;
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object* v_x_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = 22;
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object* v_x_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_743_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object* v_x_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = 25;
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object* v_x_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_748_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object* v_x_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = 29;
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object* v_x_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_753_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object* v_x_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = 33;
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_758_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object* v_x_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = 35;
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object* v_x_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object* v_x_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = 38;
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object* v_x_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_768_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object* v_x_771_){
_start:
{
uint8_t v___x_772_; 
v___x_772_ = 39;
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object* v_x_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_773_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object* v_x_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = 37;
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object* v_x_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_778_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object* v_x_781_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = 36;
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object* v_x_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_783_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object* v_x_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = 34;
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object* v_x_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_788_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object* v_x_791_){
_start:
{
uint8_t v___x_792_; 
v___x_792_ = 30;
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object* v_x_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_793_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object* v_x_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = 26;
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object* v_x_801_){
_start:
{
uint8_t v___x_802_; 
v___x_802_ = 24;
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object* v_x_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_803_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object* v_x_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = 27;
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object* v_x_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_808_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object* v_x_811_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = 21;
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object* v_x_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_813_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object* v_x_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = 19;
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object* v_x_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_818_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object* v_x_821_){
_start:
{
uint8_t v___x_822_; 
v___x_822_ = 17;
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object* v_x_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_823_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object* v_x_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = 15;
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object* v_x_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_828_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object* v_x_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = 13;
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object* v_x_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_833_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object* v_x_836_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = 11;
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object* v_x_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_838_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object* v_x_841_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = 6;
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_843_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object* v_x_846_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = 3;
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object* v_x_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object* v_x_851_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = 2;
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object* v_x_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_853_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object* v_x_856_){
_start:
{
uint8_t v___x_857_; 
v___x_857_ = 31;
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_858_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object* v_x_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = 0;
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_863_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object* v_x_866_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = 7;
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object* v_x_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_868_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object* v_x_871_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = 8;
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_873_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22));
v___x_901_ = lean_string_to_utf8(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23);
v___x_903_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26));
v___x_907_ = lean_string_to_utf8(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27);
v___x_909_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29));
v___x_912_ = lean_string_to_utf8(v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30);
v___x_914_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33));
v___x_918_ = lean_string_to_utf8(v___x_917_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34);
v___x_920_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36));
v___x_923_ = lean_string_to_utf8(v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37);
v___x_925_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40));
v___x_929_ = lean_string_to_utf8(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41);
v___x_931_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43));
v___x_934_ = lean_string_to_utf8(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44);
v___x_936_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47));
v___x_940_ = lean_string_to_utf8(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48);
v___x_942_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50));
v___x_945_ = lean_string_to_utf8(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51);
v___x_947_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54));
v___x_951_ = lean_string_to_utf8(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55);
v___x_953_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57));
v___x_956_ = lean_string_to_utf8(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58);
v___x_958_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61));
v___x_962_ = lean_string_to_utf8(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62);
v___x_964_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64));
v___x_967_ = lean_string_to_utf8(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65);
v___x_969_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68));
v___x_973_ = lean_string_to_utf8(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69);
v___x_975_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71));
v___x_978_ = lean_string_to_utf8(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72);
v___x_980_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75));
v___x_984_ = lean_string_to_utf8(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76);
v___x_986_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78));
v___x_989_ = lean_string_to_utf8(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79);
v___x_991_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82));
v___x_995_ = lean_string_to_utf8(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83);
v___x_997_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85));
v___x_1000_ = lean_string_to_utf8(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86);
v___x_1002_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89));
v___x_1006_ = lean_string_to_utf8(v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90);
v___x_1008_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92));
v___x_1011_ = lean_string_to_utf8(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93);
v___x_1013_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96));
v___x_1017_ = lean_string_to_utf8(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97);
v___x_1019_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99));
v___x_1022_ = lean_string_to_utf8(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100);
v___x_1024_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103));
v___x_1028_ = lean_string_to_utf8(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104);
v___x_1030_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106));
v___x_1033_ = lean_string_to_utf8(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107);
v___x_1035_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110));
v___x_1039_ = lean_string_to_utf8(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111);
v___x_1041_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113));
v___x_1044_ = lean_string_to_utf8(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114);
v___x_1046_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117));
v___x_1050_ = lean_string_to_utf8(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118);
v___x_1052_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120));
v___x_1055_ = lean_string_to_utf8(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121);
v___x_1057_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124));
v___x_1061_ = lean_string_to_utf8(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125);
v___x_1063_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127));
v___x_1066_ = lean_string_to_utf8(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128);
v___x_1068_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131));
v___x_1072_ = lean_string_to_utf8(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132);
v___x_1074_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134));
v___x_1077_ = lean_string_to_utf8(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135);
v___x_1079_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138));
v___x_1083_ = lean_string_to_utf8(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139);
v___x_1085_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141));
v___x_1088_ = lean_string_to_utf8(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142);
v___x_1090_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145));
v___x_1094_ = lean_string_to_utf8(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146);
v___x_1096_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148));
v___x_1099_ = lean_string_to_utf8(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149);
v___x_1101_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152));
v___x_1105_ = lean_string_to_utf8(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153);
v___x_1107_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155));
v___x_1110_ = lean_string_to_utf8(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156);
v___x_1112_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159));
v___x_1116_ = lean_string_to_utf8(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160);
v___x_1118_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_1119_){
_start:
{
lean_object* v___f_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___f_1139_; lean_object* v___f_1140_; lean_object* v_idx_1142_; lean_object* v___y_1143_; lean_object* v_pos_1144_; lean_object* v_idx_1145_; lean_object* v_idx_1180_; lean_object* v___y_1181_; lean_object* v_pos_1182_; lean_object* v_idx_1183_; lean_object* v___f_1198_; lean_object* v_idx_1200_; lean_object* v___y_1201_; lean_object* v_pos_1202_; lean_object* v_idx_1203_; lean_object* v_idx_1219_; lean_object* v___y_1220_; lean_object* v_pos_1221_; lean_object* v_idx_1222_; lean_object* v___f_1237_; lean_object* v_idx_1239_; lean_object* v___y_1240_; lean_object* v_pos_1241_; lean_object* v_idx_1242_; lean_object* v_idx_1258_; lean_object* v___y_1259_; lean_object* v_pos_1260_; lean_object* v_idx_1261_; lean_object* v___f_1276_; lean_object* v_idx_1278_; lean_object* v___y_1279_; lean_object* v_pos_1280_; lean_object* v_idx_1281_; lean_object* v_idx_1297_; lean_object* v___y_1298_; lean_object* v_pos_1299_; lean_object* v_idx_1300_; lean_object* v___f_1315_; lean_object* v_idx_1317_; lean_object* v___y_1318_; lean_object* v_pos_1319_; lean_object* v_idx_1320_; lean_object* v_idx_1336_; lean_object* v___y_1337_; lean_object* v_pos_1338_; lean_object* v_idx_1339_; lean_object* v___f_1354_; lean_object* v_idx_1356_; lean_object* v___y_1357_; lean_object* v_pos_1358_; lean_object* v_idx_1359_; lean_object* v_idx_1375_; lean_object* v___y_1376_; lean_object* v_pos_1377_; lean_object* v_idx_1378_; lean_object* v___f_1393_; lean_object* v_idx_1395_; lean_object* v___y_1396_; lean_object* v_pos_1397_; lean_object* v_idx_1398_; lean_object* v_idx_1414_; lean_object* v___y_1415_; lean_object* v_pos_1416_; lean_object* v_idx_1417_; lean_object* v___f_1432_; lean_object* v_idx_1434_; lean_object* v___y_1435_; lean_object* v_pos_1436_; lean_object* v_idx_1437_; lean_object* v_idx_1453_; lean_object* v___y_1454_; lean_object* v_pos_1455_; lean_object* v_idx_1456_; lean_object* v___f_1471_; lean_object* v_idx_1473_; lean_object* v___y_1474_; lean_object* v_pos_1475_; lean_object* v_idx_1476_; lean_object* v_idx_1492_; lean_object* v___y_1493_; lean_object* v_pos_1494_; lean_object* v_idx_1495_; lean_object* v___f_1510_; lean_object* v_idx_1512_; lean_object* v___y_1513_; lean_object* v_pos_1514_; lean_object* v_idx_1515_; lean_object* v_idx_1531_; lean_object* v___y_1532_; lean_object* v_pos_1533_; lean_object* v_idx_1534_; lean_object* v___f_1549_; lean_object* v_idx_1551_; lean_object* v___y_1552_; lean_object* v_pos_1553_; lean_object* v_idx_1554_; lean_object* v_idx_1570_; lean_object* v___y_1571_; lean_object* v_pos_1572_; lean_object* v_idx_1573_; lean_object* v___f_1588_; lean_object* v_idx_1590_; lean_object* v___y_1591_; lean_object* v_pos_1592_; lean_object* v_idx_1593_; lean_object* v_idx_1609_; lean_object* v___y_1610_; lean_object* v_pos_1611_; lean_object* v_idx_1612_; lean_object* v___f_1627_; lean_object* v_idx_1629_; lean_object* v___y_1630_; lean_object* v_pos_1631_; lean_object* v_idx_1632_; lean_object* v_idx_1648_; lean_object* v___y_1649_; lean_object* v_pos_1650_; lean_object* v_idx_1651_; lean_object* v___f_1666_; lean_object* v_idx_1668_; lean_object* v___y_1669_; lean_object* v_pos_1670_; lean_object* v_idx_1671_; lean_object* v_idx_1687_; lean_object* v___y_1688_; lean_object* v_pos_1689_; lean_object* v_idx_1690_; lean_object* v___f_1705_; lean_object* v_idx_1707_; lean_object* v___y_1708_; lean_object* v_pos_1709_; lean_object* v_idx_1710_; lean_object* v_idx_1726_; lean_object* v___y_1727_; lean_object* v_pos_1728_; lean_object* v_idx_1729_; lean_object* v___f_1744_; lean_object* v_idx_1746_; lean_object* v___y_1747_; lean_object* v_pos_1748_; lean_object* v_idx_1749_; lean_object* v_idx_1765_; lean_object* v___y_1766_; lean_object* v_pos_1767_; lean_object* v_idx_1768_; lean_object* v___f_1783_; lean_object* v_idx_1785_; lean_object* v___y_1786_; lean_object* v_pos_1787_; lean_object* v_idx_1788_; lean_object* v_idx_1804_; lean_object* v___y_1805_; lean_object* v_pos_1806_; lean_object* v_idx_1807_; lean_object* v___f_1822_; lean_object* v_idx_1824_; lean_object* v___y_1825_; lean_object* v_pos_1826_; lean_object* v_idx_1827_; lean_object* v_idx_1843_; lean_object* v___y_1844_; lean_object* v_pos_1845_; lean_object* v_idx_1846_; lean_object* v___f_1861_; lean_object* v_idx_1863_; lean_object* v___y_1864_; lean_object* v_pos_1865_; lean_object* v_idx_1866_; lean_object* v_idx_1882_; lean_object* v___y_1883_; lean_object* v_pos_1884_; lean_object* v_idx_1885_; lean_object* v___f_1900_; lean_object* v_idx_1902_; lean_object* v___y_1903_; lean_object* v_pos_1904_; lean_object* v_idx_1905_; lean_object* v___y_1921_; lean_object* v_pos_1922_; lean_object* v___f_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___f_1120_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0));
v___f_1121_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___f_1122_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2));
v___f_1123_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
v___f_1124_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4));
v___f_1125_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5));
v___f_1126_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6));
v___f_1127_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7));
v___f_1128_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8));
v___f_1129_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9));
v___f_1130_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10));
v___f_1131_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11));
v___f_1132_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12));
v___f_1133_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13));
v___f_1134_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14));
v___f_1135_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15));
v___f_1136_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16));
v___f_1137_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17));
v___f_1138_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18));
v___f_1139_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19));
v___f_1140_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___f_1198_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25));
v___f_1237_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32));
v___f_1276_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39));
v___f_1315_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46));
v___f_1354_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53));
v___f_1393_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60));
v___f_1432_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67));
v___f_1471_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74));
v___f_1510_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81));
v___f_1549_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88));
v___f_1588_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95));
v___f_1627_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102));
v___f_1666_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109));
v___f_1705_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116));
v___f_1744_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123));
v___f_1783_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130));
v___f_1822_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137));
v___f_1861_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144));
v___f_1900_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151));
v___f_1939_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158));
v___x_1940_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161);
lean_inc_ref(v_a_1119_);
v___x_1941_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1940_, v___f_1939_, v_a_1119_);
if (lean_obj_tag(v___x_1941_) == 0)
{
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_dec_ref(v_a_1119_);
return v___x_1941_;
}
else
{
lean_object* v_pos_1942_; 
v_pos_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_pos_1942_);
v___y_1921_ = v___x_1941_;
v_pos_1922_ = v_pos_1942_;
goto v___jp_1920_;
}
}
else
{
lean_object* v_err_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_err_1943_ = lean_ctor_get(v___x_1941_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1941_, 0);
lean_dec(v_unused_1951_);
v___x_1945_ = v___x_1941_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_err_1943_);
lean_dec(v___x_1941_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
lean_inc_ref(v_a_1119_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v_a_1119_);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1119_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_err_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_inc_ref(v_a_1119_);
v___y_1921_ = v___x_1948_;
v_pos_1922_ = v_a_1119_;
goto v___jp_1920_;
}
}
}
v___jp_1141_:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_nat_dec_eq(v_idx_1142_, v_idx_1145_);
lean_dec(v_idx_1145_);
lean_dec(v_idx_1142_);
if (v___x_1146_ == 0)
{
lean_dec_ref(v_pos_1144_);
return v___y_1143_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_snd_1150_; lean_object* v_snd_1151_; uint8_t v___x_1152_; 
lean_dec_ref(v___y_1143_);
v___x_1147_ = lean_unsigned_to_nat(64u);
v___x_1148_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pos_1144_);
v___x_1149_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1140_, v___x_1147_, v___x_1148_, v_pos_1144_);
v_snd_1150_ = lean_ctor_get(v___x_1149_, 1);
lean_inc(v_snd_1150_);
v_snd_1151_ = lean_ctor_get(v_snd_1150_, 1);
v___x_1152_ = lean_unbox(v_snd_1151_);
if (v___x_1152_ == 0)
{
lean_object* v_fst_1153_; lean_object* v_fst_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1167_; 
v_fst_1153_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_fst_1153_);
lean_dec_ref(v___x_1149_);
v_fst_1154_ = lean_ctor_get(v_snd_1150_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_snd_1150_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v_snd_1150_, 1);
lean_dec(v_unused_1168_);
v___x_1156_ = v_snd_1150_;
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_fst_1154_);
lean_dec(v_snd_1150_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_nat_dec_eq(v_fst_1153_, v___x_1148_);
lean_dec(v_fst_1153_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_dec_ref(v_pos_1144_);
v___x_1159_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21));
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 1);
lean_ctor_set(v___x_1156_, 1, v___x_1159_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_fst_1154_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_fst_1154_);
v___x_1163_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 1);
lean_ctor_set(v___x_1156_, 1, v___x_1163_);
lean_ctor_set(v___x_1156_, 0, v_pos_1144_);
v___x_1165_ = v___x_1156_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_pos_1144_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v_fst_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v___x_1149_);
lean_dec_ref(v_pos_1144_);
v_fst_1169_ = lean_ctor_get(v_snd_1150_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_snd_1150_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; 
v_unused_1178_ = lean_ctor_get(v_snd_1150_, 1);
lean_dec(v_unused_1178_);
v___x_1171_ = v_snd_1150_;
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_fst_1169_);
lean_dec(v_snd_1150_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(0);
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 1);
lean_ctor_set(v___x_1171_, 1, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_fst_1169_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
v___jp_1179_:
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_nat_dec_eq(v_idx_1180_, v_idx_1183_);
lean_dec(v_idx_1180_);
if (v___x_1184_ == 0)
{
lean_dec(v_idx_1183_);
lean_dec_ref(v_pos_1182_);
return v___y_1181_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec_ref(v___y_1181_);
v___x_1185_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24);
lean_inc_ref(v_pos_1182_);
v___x_1186_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1185_, v___f_1139_, v_pos_1182_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_dec_ref(v_pos_1182_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_dec(v_idx_1183_);
return v___x_1186_;
}
else
{
lean_object* v_pos_1187_; lean_object* v_idx_1188_; 
v_pos_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_pos_1187_);
v_idx_1188_ = lean_ctor_get(v_pos_1187_, 1);
lean_inc(v_idx_1188_);
v_idx_1142_ = v_idx_1183_;
v___y_1143_ = v___x_1186_;
v_pos_1144_ = v_pos_1187_;
v_idx_1145_ = v_idx_1188_;
goto v___jp_1141_;
}
}
else
{
lean_object* v_err_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
v_err_1189_ = lean_ctor_get(v___x_1186_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v___x_1186_, 0);
lean_dec(v_unused_1197_);
v___x_1191_ = v___x_1186_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_err_1189_);
lean_dec(v___x_1186_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
lean_inc_ref(v_pos_1182_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v_pos_1182_);
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_pos_1182_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_err_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_inc(v_idx_1183_);
v_idx_1142_ = v_idx_1183_;
v___y_1143_ = v___x_1194_;
v_pos_1144_ = v_pos_1182_;
v_idx_1145_ = v_idx_1183_;
goto v___jp_1141_;
}
}
}
}
}
v___jp_1199_:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_nat_dec_eq(v_idx_1200_, v_idx_1203_);
lean_dec(v_idx_1200_);
if (v___x_1204_ == 0)
{
lean_dec(v_idx_1203_);
lean_dec_ref(v_pos_1202_);
return v___y_1201_;
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec_ref(v___y_1201_);
v___x_1205_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28);
lean_inc_ref(v_pos_1202_);
v___x_1206_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1205_, v___f_1198_, v_pos_1202_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_dec_ref(v_pos_1202_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_dec(v_idx_1203_);
return v___x_1206_;
}
else
{
lean_object* v_pos_1207_; lean_object* v_idx_1208_; 
v_pos_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_pos_1207_);
v_idx_1208_ = lean_ctor_get(v_pos_1207_, 1);
lean_inc(v_idx_1208_);
v_idx_1180_ = v_idx_1203_;
v___y_1181_ = v___x_1206_;
v_pos_1182_ = v_pos_1207_;
v_idx_1183_ = v_idx_1208_;
goto v___jp_1179_;
}
}
else
{
lean_object* v_err_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_err_1209_ = lean_ctor_get(v___x_1206_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1206_, 0);
lean_dec(v_unused_1217_);
v___x_1211_ = v___x_1206_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_err_1209_);
lean_dec(v___x_1206_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
lean_inc_ref(v_pos_1202_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_pos_1202_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_pos_1202_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_err_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_inc(v_idx_1203_);
v_idx_1180_ = v_idx_1203_;
v___y_1181_ = v___x_1214_;
v_pos_1182_ = v_pos_1202_;
v_idx_1183_ = v_idx_1203_;
goto v___jp_1179_;
}
}
}
}
}
v___jp_1218_:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_nat_dec_eq(v_idx_1219_, v_idx_1222_);
lean_dec(v_idx_1219_);
if (v___x_1223_ == 0)
{
lean_dec(v_idx_1222_);
lean_dec_ref(v_pos_1221_);
return v___y_1220_;
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec_ref(v___y_1220_);
v___x_1224_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31);
lean_inc_ref(v_pos_1221_);
v___x_1225_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1224_, v___f_1138_, v_pos_1221_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_dec_ref(v_pos_1221_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_dec(v_idx_1222_);
return v___x_1225_;
}
else
{
lean_object* v_pos_1226_; lean_object* v_idx_1227_; 
v_pos_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_pos_1226_);
v_idx_1227_ = lean_ctor_get(v_pos_1226_, 1);
lean_inc(v_idx_1227_);
v_idx_1200_ = v_idx_1222_;
v___y_1201_ = v___x_1225_;
v_pos_1202_ = v_pos_1226_;
v_idx_1203_ = v_idx_1227_;
goto v___jp_1199_;
}
}
else
{
lean_object* v_err_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_err_1228_ = lean_ctor_get(v___x_1225_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1225_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v___x_1225_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_err_1228_);
lean_dec(v___x_1225_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
lean_inc_ref(v_pos_1221_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_pos_1221_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_pos_1221_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_err_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_inc(v_idx_1222_);
v_idx_1200_ = v_idx_1222_;
v___y_1201_ = v___x_1233_;
v_pos_1202_ = v_pos_1221_;
v_idx_1203_ = v_idx_1222_;
goto v___jp_1199_;
}
}
}
}
}
v___jp_1238_:
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_nat_dec_eq(v_idx_1239_, v_idx_1242_);
lean_dec(v_idx_1239_);
if (v___x_1243_ == 0)
{
lean_dec(v_idx_1242_);
lean_dec_ref(v_pos_1241_);
return v___y_1240_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v___y_1240_);
v___x_1244_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35);
lean_inc_ref(v_pos_1241_);
v___x_1245_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1244_, v___f_1237_, v_pos_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_dec_ref(v_pos_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_dec(v_idx_1242_);
return v___x_1245_;
}
else
{
lean_object* v_pos_1246_; lean_object* v_idx_1247_; 
v_pos_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_pos_1246_);
v_idx_1247_ = lean_ctor_get(v_pos_1246_, 1);
lean_inc(v_idx_1247_);
v_idx_1219_ = v_idx_1242_;
v___y_1220_ = v___x_1245_;
v_pos_1221_ = v_pos_1246_;
v_idx_1222_ = v_idx_1247_;
goto v___jp_1218_;
}
}
else
{
lean_object* v_err_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_err_1248_ = lean_ctor_get(v___x_1245_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1245_, 0);
lean_dec(v_unused_1256_);
v___x_1250_ = v___x_1245_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_err_1248_);
lean_dec(v___x_1245_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
lean_inc_ref(v_pos_1241_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v_pos_1241_);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_pos_1241_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_err_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_inc(v_idx_1242_);
v_idx_1219_ = v_idx_1242_;
v___y_1220_ = v___x_1253_;
v_pos_1221_ = v_pos_1241_;
v_idx_1222_ = v_idx_1242_;
goto v___jp_1218_;
}
}
}
}
}
v___jp_1257_:
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_nat_dec_eq(v_idx_1258_, v_idx_1261_);
lean_dec(v_idx_1258_);
if (v___x_1262_ == 0)
{
lean_dec(v_idx_1261_);
lean_dec_ref(v_pos_1260_);
return v___y_1259_;
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref(v___y_1259_);
v___x_1263_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38);
lean_inc_ref(v_pos_1260_);
v___x_1264_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1263_, v___f_1137_, v_pos_1260_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_dec_ref(v_pos_1260_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_dec(v_idx_1261_);
return v___x_1264_;
}
else
{
lean_object* v_pos_1265_; lean_object* v_idx_1266_; 
v_pos_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_pos_1265_);
v_idx_1266_ = lean_ctor_get(v_pos_1265_, 1);
lean_inc(v_idx_1266_);
v_idx_1239_ = v_idx_1261_;
v___y_1240_ = v___x_1264_;
v_pos_1241_ = v_pos_1265_;
v_idx_1242_ = v_idx_1266_;
goto v___jp_1238_;
}
}
else
{
lean_object* v_err_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_err_1267_ = lean_ctor_get(v___x_1264_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1275_);
v___x_1269_ = v___x_1264_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_err_1267_);
lean_dec(v___x_1264_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
lean_inc_ref(v_pos_1260_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_pos_1260_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_pos_1260_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_err_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_inc(v_idx_1261_);
v_idx_1239_ = v_idx_1261_;
v___y_1240_ = v___x_1272_;
v_pos_1241_ = v_pos_1260_;
v_idx_1242_ = v_idx_1261_;
goto v___jp_1238_;
}
}
}
}
}
v___jp_1277_:
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_nat_dec_eq(v_idx_1278_, v_idx_1281_);
lean_dec(v_idx_1278_);
if (v___x_1282_ == 0)
{
lean_dec(v_idx_1281_);
lean_dec_ref(v_pos_1280_);
return v___y_1279_;
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec_ref(v___y_1279_);
v___x_1283_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42);
lean_inc_ref(v_pos_1280_);
v___x_1284_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1283_, v___f_1276_, v_pos_1280_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec_ref(v_pos_1280_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec(v_idx_1281_);
return v___x_1284_;
}
else
{
lean_object* v_pos_1285_; lean_object* v_idx_1286_; 
v_pos_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_pos_1285_);
v_idx_1286_ = lean_ctor_get(v_pos_1285_, 1);
lean_inc(v_idx_1286_);
v_idx_1258_ = v_idx_1281_;
v___y_1259_ = v___x_1284_;
v_pos_1260_ = v_pos_1285_;
v_idx_1261_ = v_idx_1286_;
goto v___jp_1257_;
}
}
else
{
lean_object* v_err_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_err_1287_ = lean_ctor_get(v___x_1284_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1284_, 0);
lean_dec(v_unused_1295_);
v___x_1289_ = v___x_1284_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_err_1287_);
lean_dec(v___x_1284_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
lean_inc_ref(v_pos_1280_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v_pos_1280_);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_pos_1280_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_err_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_inc(v_idx_1281_);
v_idx_1258_ = v_idx_1281_;
v___y_1259_ = v___x_1292_;
v_pos_1260_ = v_pos_1280_;
v_idx_1261_ = v_idx_1281_;
goto v___jp_1257_;
}
}
}
}
}
v___jp_1296_:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_nat_dec_eq(v_idx_1297_, v_idx_1300_);
lean_dec(v_idx_1297_);
if (v___x_1301_ == 0)
{
lean_dec(v_idx_1300_);
lean_dec_ref(v_pos_1299_);
return v___y_1298_;
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec_ref(v___y_1298_);
v___x_1302_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45);
lean_inc_ref(v_pos_1299_);
v___x_1303_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1302_, v___f_1136_, v_pos_1299_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_dec_ref(v_pos_1299_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_dec(v_idx_1300_);
return v___x_1303_;
}
else
{
lean_object* v_pos_1304_; lean_object* v_idx_1305_; 
v_pos_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_pos_1304_);
v_idx_1305_ = lean_ctor_get(v_pos_1304_, 1);
lean_inc(v_idx_1305_);
v_idx_1278_ = v_idx_1300_;
v___y_1279_ = v___x_1303_;
v_pos_1280_ = v_pos_1304_;
v_idx_1281_ = v_idx_1305_;
goto v___jp_1277_;
}
}
else
{
lean_object* v_err_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_err_1306_ = lean_ctor_get(v___x_1303_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1303_, 0);
lean_dec(v_unused_1314_);
v___x_1308_ = v___x_1303_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_err_1306_);
lean_dec(v___x_1303_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
lean_inc_ref(v_pos_1299_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_pos_1299_);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_pos_1299_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_err_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_inc(v_idx_1300_);
v_idx_1278_ = v_idx_1300_;
v___y_1279_ = v___x_1311_;
v_pos_1280_ = v_pos_1299_;
v_idx_1281_ = v_idx_1300_;
goto v___jp_1277_;
}
}
}
}
}
v___jp_1316_:
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_nat_dec_eq(v_idx_1317_, v_idx_1320_);
lean_dec(v_idx_1317_);
if (v___x_1321_ == 0)
{
lean_dec(v_idx_1320_);
lean_dec_ref(v_pos_1319_);
return v___y_1318_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec_ref(v___y_1318_);
v___x_1322_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49);
lean_inc_ref(v_pos_1319_);
v___x_1323_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1322_, v___f_1315_, v_pos_1319_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_dec_ref(v_pos_1319_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_dec(v_idx_1320_);
return v___x_1323_;
}
else
{
lean_object* v_pos_1324_; lean_object* v_idx_1325_; 
v_pos_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_pos_1324_);
v_idx_1325_ = lean_ctor_get(v_pos_1324_, 1);
lean_inc(v_idx_1325_);
v_idx_1297_ = v_idx_1320_;
v___y_1298_ = v___x_1323_;
v_pos_1299_ = v_pos_1324_;
v_idx_1300_ = v_idx_1325_;
goto v___jp_1296_;
}
}
else
{
lean_object* v_err_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_err_1326_ = lean_ctor_get(v___x_1323_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v___x_1323_, 0);
lean_dec(v_unused_1334_);
v___x_1328_ = v___x_1323_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_err_1326_);
lean_dec(v___x_1323_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
lean_inc_ref(v_pos_1319_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_pos_1319_);
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_pos_1319_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_err_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_inc(v_idx_1320_);
v_idx_1297_ = v_idx_1320_;
v___y_1298_ = v___x_1331_;
v_pos_1299_ = v_pos_1319_;
v_idx_1300_ = v_idx_1320_;
goto v___jp_1296_;
}
}
}
}
}
v___jp_1335_:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_nat_dec_eq(v_idx_1336_, v_idx_1339_);
lean_dec(v_idx_1336_);
if (v___x_1340_ == 0)
{
lean_dec(v_idx_1339_);
lean_dec_ref(v_pos_1338_);
return v___y_1337_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v___y_1337_);
v___x_1341_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52);
lean_inc_ref(v_pos_1338_);
v___x_1342_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1341_, v___f_1135_, v_pos_1338_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_dec_ref(v_pos_1338_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_dec(v_idx_1339_);
return v___x_1342_;
}
else
{
lean_object* v_pos_1343_; lean_object* v_idx_1344_; 
v_pos_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_pos_1343_);
v_idx_1344_ = lean_ctor_get(v_pos_1343_, 1);
lean_inc(v_idx_1344_);
v_idx_1317_ = v_idx_1339_;
v___y_1318_ = v___x_1342_;
v_pos_1319_ = v_pos_1343_;
v_idx_1320_ = v_idx_1344_;
goto v___jp_1316_;
}
}
else
{
lean_object* v_err_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_err_1345_ = lean_ctor_get(v___x_1342_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v___x_1342_, 0);
lean_dec(v_unused_1353_);
v___x_1347_ = v___x_1342_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_err_1345_);
lean_dec(v___x_1342_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
lean_inc_ref(v_pos_1338_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v_pos_1338_);
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_pos_1338_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_err_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_inc(v_idx_1339_);
v_idx_1317_ = v_idx_1339_;
v___y_1318_ = v___x_1350_;
v_pos_1319_ = v_pos_1338_;
v_idx_1320_ = v_idx_1339_;
goto v___jp_1316_;
}
}
}
}
}
v___jp_1355_:
{
uint8_t v___x_1360_; 
v___x_1360_ = lean_nat_dec_eq(v_idx_1356_, v_idx_1359_);
lean_dec(v_idx_1356_);
if (v___x_1360_ == 0)
{
lean_dec(v_idx_1359_);
lean_dec_ref(v_pos_1358_);
return v___y_1357_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec_ref(v___y_1357_);
v___x_1361_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56);
lean_inc_ref(v_pos_1358_);
v___x_1362_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1361_, v___f_1354_, v_pos_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_dec_ref(v_pos_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_dec(v_idx_1359_);
return v___x_1362_;
}
else
{
lean_object* v_pos_1363_; lean_object* v_idx_1364_; 
v_pos_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_pos_1363_);
v_idx_1364_ = lean_ctor_get(v_pos_1363_, 1);
lean_inc(v_idx_1364_);
v_idx_1336_ = v_idx_1359_;
v___y_1337_ = v___x_1362_;
v_pos_1338_ = v_pos_1363_;
v_idx_1339_ = v_idx_1364_;
goto v___jp_1335_;
}
}
else
{
lean_object* v_err_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_err_1365_ = lean_ctor_get(v___x_1362_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___x_1362_, 0);
lean_dec(v_unused_1373_);
v___x_1367_ = v___x_1362_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_err_1365_);
lean_dec(v___x_1362_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
lean_inc_ref(v_pos_1358_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v_pos_1358_);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_pos_1358_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_err_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_inc(v_idx_1359_);
v_idx_1336_ = v_idx_1359_;
v___y_1337_ = v___x_1370_;
v_pos_1338_ = v_pos_1358_;
v_idx_1339_ = v_idx_1359_;
goto v___jp_1335_;
}
}
}
}
}
v___jp_1374_:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_nat_dec_eq(v_idx_1375_, v_idx_1378_);
lean_dec(v_idx_1375_);
if (v___x_1379_ == 0)
{
lean_dec(v_idx_1378_);
lean_dec_ref(v_pos_1377_);
return v___y_1376_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v___y_1376_);
v___x_1380_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59);
lean_inc_ref(v_pos_1377_);
v___x_1381_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1380_, v___f_1134_, v_pos_1377_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_dec_ref(v_pos_1377_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_dec(v_idx_1378_);
return v___x_1381_;
}
else
{
lean_object* v_pos_1382_; lean_object* v_idx_1383_; 
v_pos_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_pos_1382_);
v_idx_1383_ = lean_ctor_get(v_pos_1382_, 1);
lean_inc(v_idx_1383_);
v_idx_1356_ = v_idx_1378_;
v___y_1357_ = v___x_1381_;
v_pos_1358_ = v_pos_1382_;
v_idx_1359_ = v_idx_1383_;
goto v___jp_1355_;
}
}
else
{
lean_object* v_err_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_err_1384_ = lean_ctor_get(v___x_1381_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1392_);
v___x_1386_ = v___x_1381_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_err_1384_);
lean_dec(v___x_1381_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
lean_inc_ref(v_pos_1377_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v_pos_1377_);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_pos_1377_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_err_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_inc(v_idx_1378_);
v_idx_1356_ = v_idx_1378_;
v___y_1357_ = v___x_1389_;
v_pos_1358_ = v_pos_1377_;
v_idx_1359_ = v_idx_1378_;
goto v___jp_1355_;
}
}
}
}
}
v___jp_1394_:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_eq(v_idx_1395_, v_idx_1398_);
lean_dec(v_idx_1395_);
if (v___x_1399_ == 0)
{
lean_dec(v_idx_1398_);
lean_dec_ref(v_pos_1397_);
return v___y_1396_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref(v___y_1396_);
v___x_1400_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63);
lean_inc_ref(v_pos_1397_);
v___x_1401_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1400_, v___f_1393_, v_pos_1397_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_dec_ref(v_pos_1397_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_dec(v_idx_1398_);
return v___x_1401_;
}
else
{
lean_object* v_pos_1402_; lean_object* v_idx_1403_; 
v_pos_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_pos_1402_);
v_idx_1403_ = lean_ctor_get(v_pos_1402_, 1);
lean_inc(v_idx_1403_);
v_idx_1375_ = v_idx_1398_;
v___y_1376_ = v___x_1401_;
v_pos_1377_ = v_pos_1402_;
v_idx_1378_ = v_idx_1403_;
goto v___jp_1374_;
}
}
else
{
lean_object* v_err_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_err_1404_ = lean_ctor_get(v___x_1401_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1412_);
v___x_1406_ = v___x_1401_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_err_1404_);
lean_dec(v___x_1401_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
lean_inc_ref(v_pos_1397_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_pos_1397_);
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_pos_1397_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_err_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_inc(v_idx_1398_);
v_idx_1375_ = v_idx_1398_;
v___y_1376_ = v___x_1409_;
v_pos_1377_ = v_pos_1397_;
v_idx_1378_ = v_idx_1398_;
goto v___jp_1374_;
}
}
}
}
}
v___jp_1413_:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_nat_dec_eq(v_idx_1414_, v_idx_1417_);
lean_dec(v_idx_1414_);
if (v___x_1418_ == 0)
{
lean_dec(v_idx_1417_);
lean_dec_ref(v_pos_1416_);
return v___y_1415_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v___y_1415_);
v___x_1419_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66);
lean_inc_ref(v_pos_1416_);
v___x_1420_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1419_, v___f_1133_, v_pos_1416_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_dec_ref(v_pos_1416_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_dec(v_idx_1417_);
return v___x_1420_;
}
else
{
lean_object* v_pos_1421_; lean_object* v_idx_1422_; 
v_pos_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_pos_1421_);
v_idx_1422_ = lean_ctor_get(v_pos_1421_, 1);
lean_inc(v_idx_1422_);
v_idx_1395_ = v_idx_1417_;
v___y_1396_ = v___x_1420_;
v_pos_1397_ = v_pos_1421_;
v_idx_1398_ = v_idx_1422_;
goto v___jp_1394_;
}
}
else
{
lean_object* v_err_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
v_err_1423_ = lean_ctor_get(v___x_1420_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v___x_1420_, 0);
lean_dec(v_unused_1431_);
v___x_1425_ = v___x_1420_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_err_1423_);
lean_dec(v___x_1420_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
lean_inc_ref(v_pos_1416_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v_pos_1416_);
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_pos_1416_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_err_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_inc(v_idx_1417_);
v_idx_1395_ = v_idx_1417_;
v___y_1396_ = v___x_1428_;
v_pos_1397_ = v_pos_1416_;
v_idx_1398_ = v_idx_1417_;
goto v___jp_1394_;
}
}
}
}
}
v___jp_1433_:
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_eq(v_idx_1434_, v_idx_1437_);
lean_dec(v_idx_1434_);
if (v___x_1438_ == 0)
{
lean_dec(v_idx_1437_);
lean_dec_ref(v_pos_1436_);
return v___y_1435_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v___y_1435_);
v___x_1439_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70);
lean_inc_ref(v_pos_1436_);
v___x_1440_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1439_, v___f_1432_, v_pos_1436_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_dec_ref(v_pos_1436_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_dec(v_idx_1437_);
return v___x_1440_;
}
else
{
lean_object* v_pos_1441_; lean_object* v_idx_1442_; 
v_pos_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_pos_1441_);
v_idx_1442_ = lean_ctor_get(v_pos_1441_, 1);
lean_inc(v_idx_1442_);
v_idx_1414_ = v_idx_1437_;
v___y_1415_ = v___x_1440_;
v_pos_1416_ = v_pos_1441_;
v_idx_1417_ = v_idx_1442_;
goto v___jp_1413_;
}
}
else
{
lean_object* v_err_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
v_err_1443_ = lean_ctor_get(v___x_1440_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v___x_1440_, 0);
lean_dec(v_unused_1451_);
v___x_1445_ = v___x_1440_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_err_1443_);
lean_dec(v___x_1440_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
lean_inc_ref(v_pos_1436_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v_pos_1436_);
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_pos_1436_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_err_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_inc(v_idx_1437_);
v_idx_1414_ = v_idx_1437_;
v___y_1415_ = v___x_1448_;
v_pos_1416_ = v_pos_1436_;
v_idx_1417_ = v_idx_1437_;
goto v___jp_1413_;
}
}
}
}
}
v___jp_1452_:
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_nat_dec_eq(v_idx_1453_, v_idx_1456_);
lean_dec(v_idx_1453_);
if (v___x_1457_ == 0)
{
lean_dec(v_idx_1456_);
lean_dec_ref(v_pos_1455_);
return v___y_1454_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v___y_1454_);
v___x_1458_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73);
lean_inc_ref(v_pos_1455_);
v___x_1459_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1458_, v___f_1132_, v_pos_1455_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_dec_ref(v_pos_1455_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_dec(v_idx_1456_);
return v___x_1459_;
}
else
{
lean_object* v_pos_1460_; lean_object* v_idx_1461_; 
v_pos_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_pos_1460_);
v_idx_1461_ = lean_ctor_get(v_pos_1460_, 1);
lean_inc(v_idx_1461_);
v_idx_1434_ = v_idx_1456_;
v___y_1435_ = v___x_1459_;
v_pos_1436_ = v_pos_1460_;
v_idx_1437_ = v_idx_1461_;
goto v___jp_1433_;
}
}
else
{
lean_object* v_err_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_err_1462_ = lean_ctor_get(v___x_1459_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1459_, 0);
lean_dec(v_unused_1470_);
v___x_1464_ = v___x_1459_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_err_1462_);
lean_dec(v___x_1459_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
lean_inc_ref(v_pos_1455_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_pos_1455_);
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_pos_1455_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_err_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_inc(v_idx_1456_);
v_idx_1434_ = v_idx_1456_;
v___y_1435_ = v___x_1467_;
v_pos_1436_ = v_pos_1455_;
v_idx_1437_ = v_idx_1456_;
goto v___jp_1433_;
}
}
}
}
}
v___jp_1472_:
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_nat_dec_eq(v_idx_1473_, v_idx_1476_);
lean_dec(v_idx_1473_);
if (v___x_1477_ == 0)
{
lean_dec(v_idx_1476_);
lean_dec_ref(v_pos_1475_);
return v___y_1474_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v___y_1474_);
v___x_1478_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77);
lean_inc_ref(v_pos_1475_);
v___x_1479_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1478_, v___f_1471_, v_pos_1475_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_dec_ref(v_pos_1475_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_dec(v_idx_1476_);
return v___x_1479_;
}
else
{
lean_object* v_pos_1480_; lean_object* v_idx_1481_; 
v_pos_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_pos_1480_);
v_idx_1481_ = lean_ctor_get(v_pos_1480_, 1);
lean_inc(v_idx_1481_);
v_idx_1453_ = v_idx_1476_;
v___y_1454_ = v___x_1479_;
v_pos_1455_ = v_pos_1480_;
v_idx_1456_ = v_idx_1481_;
goto v___jp_1452_;
}
}
else
{
lean_object* v_err_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_err_1482_ = lean_ctor_get(v___x_1479_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v___x_1479_, 0);
lean_dec(v_unused_1490_);
v___x_1484_ = v___x_1479_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_err_1482_);
lean_dec(v___x_1479_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
lean_inc_ref(v_pos_1475_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v_pos_1475_);
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_pos_1475_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_err_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_inc(v_idx_1476_);
v_idx_1453_ = v_idx_1476_;
v___y_1454_ = v___x_1487_;
v_pos_1455_ = v_pos_1475_;
v_idx_1456_ = v_idx_1476_;
goto v___jp_1452_;
}
}
}
}
}
v___jp_1491_:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_eq(v_idx_1492_, v_idx_1495_);
lean_dec(v_idx_1492_);
if (v___x_1496_ == 0)
{
lean_dec(v_idx_1495_);
lean_dec_ref(v_pos_1494_);
return v___y_1493_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec_ref(v___y_1493_);
v___x_1497_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80);
lean_inc_ref(v_pos_1494_);
v___x_1498_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1497_, v___f_1131_, v_pos_1494_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_dec_ref(v_pos_1494_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_dec(v_idx_1495_);
return v___x_1498_;
}
else
{
lean_object* v_pos_1499_; lean_object* v_idx_1500_; 
v_pos_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_pos_1499_);
v_idx_1500_ = lean_ctor_get(v_pos_1499_, 1);
lean_inc(v_idx_1500_);
v_idx_1473_ = v_idx_1495_;
v___y_1474_ = v___x_1498_;
v_pos_1475_ = v_pos_1499_;
v_idx_1476_ = v_idx_1500_;
goto v___jp_1472_;
}
}
else
{
lean_object* v_err_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_err_1501_ = lean_ctor_get(v___x_1498_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v___x_1498_, 0);
lean_dec(v_unused_1509_);
v___x_1503_ = v___x_1498_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_err_1501_);
lean_dec(v___x_1498_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
lean_inc_ref(v_pos_1494_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v_pos_1494_);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_pos_1494_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_err_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_inc(v_idx_1495_);
v_idx_1473_ = v_idx_1495_;
v___y_1474_ = v___x_1506_;
v_pos_1475_ = v_pos_1494_;
v_idx_1476_ = v_idx_1495_;
goto v___jp_1472_;
}
}
}
}
}
v___jp_1511_:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_nat_dec_eq(v_idx_1512_, v_idx_1515_);
lean_dec(v_idx_1512_);
if (v___x_1516_ == 0)
{
lean_dec(v_idx_1515_);
lean_dec_ref(v_pos_1514_);
return v___y_1513_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec_ref(v___y_1513_);
v___x_1517_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84);
lean_inc_ref(v_pos_1514_);
v___x_1518_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1517_, v___f_1510_, v_pos_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_dec_ref(v_pos_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_dec(v_idx_1515_);
return v___x_1518_;
}
else
{
lean_object* v_pos_1519_; lean_object* v_idx_1520_; 
v_pos_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_pos_1519_);
v_idx_1520_ = lean_ctor_get(v_pos_1519_, 1);
lean_inc(v_idx_1520_);
v_idx_1492_ = v_idx_1515_;
v___y_1493_ = v___x_1518_;
v_pos_1494_ = v_pos_1519_;
v_idx_1495_ = v_idx_1520_;
goto v___jp_1491_;
}
}
else
{
lean_object* v_err_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
v_err_1521_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v___x_1518_, 0);
lean_dec(v_unused_1529_);
v___x_1523_ = v___x_1518_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_err_1521_);
lean_dec(v___x_1518_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
lean_inc_ref(v_pos_1514_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_pos_1514_);
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_pos_1514_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_err_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_inc(v_idx_1515_);
v_idx_1492_ = v_idx_1515_;
v___y_1493_ = v___x_1526_;
v_pos_1494_ = v_pos_1514_;
v_idx_1495_ = v_idx_1515_;
goto v___jp_1491_;
}
}
}
}
}
v___jp_1530_:
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_nat_dec_eq(v_idx_1531_, v_idx_1534_);
lean_dec(v_idx_1531_);
if (v___x_1535_ == 0)
{
lean_dec(v_idx_1534_);
lean_dec_ref(v_pos_1533_);
return v___y_1532_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref(v___y_1532_);
v___x_1536_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87);
lean_inc_ref(v_pos_1533_);
v___x_1537_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1536_, v___f_1130_, v_pos_1533_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_dec_ref(v_pos_1533_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_dec(v_idx_1534_);
return v___x_1537_;
}
else
{
lean_object* v_pos_1538_; lean_object* v_idx_1539_; 
v_pos_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_pos_1538_);
v_idx_1539_ = lean_ctor_get(v_pos_1538_, 1);
lean_inc(v_idx_1539_);
v_idx_1512_ = v_idx_1534_;
v___y_1513_ = v___x_1537_;
v_pos_1514_ = v_pos_1538_;
v_idx_1515_ = v_idx_1539_;
goto v___jp_1511_;
}
}
else
{
lean_object* v_err_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_err_1540_ = lean_ctor_get(v___x_1537_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1537_, 0);
lean_dec(v_unused_1548_);
v___x_1542_ = v___x_1537_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_err_1540_);
lean_dec(v___x_1537_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
lean_inc_ref(v_pos_1533_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_pos_1533_);
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_pos_1533_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_err_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_inc(v_idx_1534_);
v_idx_1512_ = v_idx_1534_;
v___y_1513_ = v___x_1545_;
v_pos_1514_ = v_pos_1533_;
v_idx_1515_ = v_idx_1534_;
goto v___jp_1511_;
}
}
}
}
}
v___jp_1550_:
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_nat_dec_eq(v_idx_1551_, v_idx_1554_);
lean_dec(v_idx_1551_);
if (v___x_1555_ == 0)
{
lean_dec(v_idx_1554_);
lean_dec_ref(v_pos_1553_);
return v___y_1552_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref(v___y_1552_);
v___x_1556_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91);
lean_inc_ref(v_pos_1553_);
v___x_1557_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1556_, v___f_1549_, v_pos_1553_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec_ref(v_pos_1553_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec(v_idx_1554_);
return v___x_1557_;
}
else
{
lean_object* v_pos_1558_; lean_object* v_idx_1559_; 
v_pos_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_pos_1558_);
v_idx_1559_ = lean_ctor_get(v_pos_1558_, 1);
lean_inc(v_idx_1559_);
v_idx_1531_ = v_idx_1554_;
v___y_1532_ = v___x_1557_;
v_pos_1533_ = v_pos_1558_;
v_idx_1534_ = v_idx_1559_;
goto v___jp_1530_;
}
}
else
{
lean_object* v_err_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_err_1560_ = lean_ctor_get(v___x_1557_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v___x_1557_, 0);
lean_dec(v_unused_1568_);
v___x_1562_ = v___x_1557_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_err_1560_);
lean_dec(v___x_1557_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
lean_inc_ref(v_pos_1553_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v_pos_1553_);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_pos_1553_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_err_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_inc(v_idx_1554_);
v_idx_1531_ = v_idx_1554_;
v___y_1532_ = v___x_1565_;
v_pos_1533_ = v_pos_1553_;
v_idx_1534_ = v_idx_1554_;
goto v___jp_1530_;
}
}
}
}
}
v___jp_1569_:
{
uint8_t v___x_1574_; 
v___x_1574_ = lean_nat_dec_eq(v_idx_1570_, v_idx_1573_);
lean_dec(v_idx_1570_);
if (v___x_1574_ == 0)
{
lean_dec(v_idx_1573_);
lean_dec_ref(v_pos_1572_);
return v___y_1571_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec_ref(v___y_1571_);
v___x_1575_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94);
lean_inc_ref(v_pos_1572_);
v___x_1576_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1575_, v___f_1129_, v_pos_1572_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_dec_ref(v_pos_1572_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_dec(v_idx_1573_);
return v___x_1576_;
}
else
{
lean_object* v_pos_1577_; lean_object* v_idx_1578_; 
v_pos_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_pos_1577_);
v_idx_1578_ = lean_ctor_get(v_pos_1577_, 1);
lean_inc(v_idx_1578_);
v_idx_1551_ = v_idx_1573_;
v___y_1552_ = v___x_1576_;
v_pos_1553_ = v_pos_1577_;
v_idx_1554_ = v_idx_1578_;
goto v___jp_1550_;
}
}
else
{
lean_object* v_err_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_err_1579_ = lean_ctor_get(v___x_1576_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v___x_1576_, 0);
lean_dec(v_unused_1587_);
v___x_1581_ = v___x_1576_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_err_1579_);
lean_dec(v___x_1576_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
lean_inc_ref(v_pos_1572_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v_pos_1572_);
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_pos_1572_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_err_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_inc(v_idx_1573_);
v_idx_1551_ = v_idx_1573_;
v___y_1552_ = v___x_1584_;
v_pos_1553_ = v_pos_1572_;
v_idx_1554_ = v_idx_1573_;
goto v___jp_1550_;
}
}
}
}
}
v___jp_1589_:
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_nat_dec_eq(v_idx_1590_, v_idx_1593_);
lean_dec(v_idx_1590_);
if (v___x_1594_ == 0)
{
lean_dec(v_idx_1593_);
lean_dec_ref(v_pos_1592_);
return v___y_1591_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v___y_1591_);
v___x_1595_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98);
lean_inc_ref(v_pos_1592_);
v___x_1596_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1595_, v___f_1588_, v_pos_1592_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_dec_ref(v_pos_1592_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_dec(v_idx_1593_);
return v___x_1596_;
}
else
{
lean_object* v_pos_1597_; lean_object* v_idx_1598_; 
v_pos_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_pos_1597_);
v_idx_1598_ = lean_ctor_get(v_pos_1597_, 1);
lean_inc(v_idx_1598_);
v_idx_1570_ = v_idx_1593_;
v___y_1571_ = v___x_1596_;
v_pos_1572_ = v_pos_1597_;
v_idx_1573_ = v_idx_1598_;
goto v___jp_1569_;
}
}
else
{
lean_object* v_err_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_err_1599_ = lean_ctor_get(v___x_1596_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1596_, 0);
lean_dec(v_unused_1607_);
v___x_1601_ = v___x_1596_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_err_1599_);
lean_dec(v___x_1596_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
lean_inc_ref(v_pos_1592_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_pos_1592_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_pos_1592_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_err_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_inc(v_idx_1593_);
v_idx_1570_ = v_idx_1593_;
v___y_1571_ = v___x_1604_;
v_pos_1572_ = v_pos_1592_;
v_idx_1573_ = v_idx_1593_;
goto v___jp_1569_;
}
}
}
}
}
v___jp_1608_:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_nat_dec_eq(v_idx_1609_, v_idx_1612_);
lean_dec(v_idx_1609_);
if (v___x_1613_ == 0)
{
lean_dec(v_idx_1612_);
lean_dec_ref(v_pos_1611_);
return v___y_1610_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec_ref(v___y_1610_);
v___x_1614_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101);
lean_inc_ref(v_pos_1611_);
v___x_1615_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1614_, v___f_1128_, v_pos_1611_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_dec_ref(v_pos_1611_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_dec(v_idx_1612_);
return v___x_1615_;
}
else
{
lean_object* v_pos_1616_; lean_object* v_idx_1617_; 
v_pos_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_pos_1616_);
v_idx_1617_ = lean_ctor_get(v_pos_1616_, 1);
lean_inc(v_idx_1617_);
v_idx_1590_ = v_idx_1612_;
v___y_1591_ = v___x_1615_;
v_pos_1592_ = v_pos_1616_;
v_idx_1593_ = v_idx_1617_;
goto v___jp_1589_;
}
}
else
{
lean_object* v_err_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_err_1618_ = lean_ctor_get(v___x_1615_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v___x_1615_, 0);
lean_dec(v_unused_1626_);
v___x_1620_ = v___x_1615_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_err_1618_);
lean_dec(v___x_1615_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
lean_inc_ref(v_pos_1611_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_pos_1611_);
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_pos_1611_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_err_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_inc(v_idx_1612_);
v_idx_1590_ = v_idx_1612_;
v___y_1591_ = v___x_1623_;
v_pos_1592_ = v_pos_1611_;
v_idx_1593_ = v_idx_1612_;
goto v___jp_1589_;
}
}
}
}
}
v___jp_1628_:
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_nat_dec_eq(v_idx_1629_, v_idx_1632_);
lean_dec(v_idx_1629_);
if (v___x_1633_ == 0)
{
lean_dec(v_idx_1632_);
lean_dec_ref(v_pos_1631_);
return v___y_1630_;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref(v___y_1630_);
v___x_1634_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105);
lean_inc_ref(v_pos_1631_);
v___x_1635_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1634_, v___f_1627_, v_pos_1631_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_dec_ref(v_pos_1631_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_dec(v_idx_1632_);
return v___x_1635_;
}
else
{
lean_object* v_pos_1636_; lean_object* v_idx_1637_; 
v_pos_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_pos_1636_);
v_idx_1637_ = lean_ctor_get(v_pos_1636_, 1);
lean_inc(v_idx_1637_);
v_idx_1609_ = v_idx_1632_;
v___y_1610_ = v___x_1635_;
v_pos_1611_ = v_pos_1636_;
v_idx_1612_ = v_idx_1637_;
goto v___jp_1608_;
}
}
else
{
lean_object* v_err_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_err_1638_ = lean_ctor_get(v___x_1635_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1635_, 0);
lean_dec(v_unused_1646_);
v___x_1640_ = v___x_1635_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_err_1638_);
lean_dec(v___x_1635_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
lean_inc_ref(v_pos_1631_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v_pos_1631_);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_pos_1631_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_err_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_inc(v_idx_1632_);
v_idx_1609_ = v_idx_1632_;
v___y_1610_ = v___x_1643_;
v_pos_1611_ = v_pos_1631_;
v_idx_1612_ = v_idx_1632_;
goto v___jp_1608_;
}
}
}
}
}
v___jp_1647_:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_nat_dec_eq(v_idx_1648_, v_idx_1651_);
lean_dec(v_idx_1648_);
if (v___x_1652_ == 0)
{
lean_dec(v_idx_1651_);
lean_dec_ref(v_pos_1650_);
return v___y_1649_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v___y_1649_);
v___x_1653_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108);
lean_inc_ref(v_pos_1650_);
v___x_1654_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1653_, v___f_1127_, v_pos_1650_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_dec_ref(v_pos_1650_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_dec(v_idx_1651_);
return v___x_1654_;
}
else
{
lean_object* v_pos_1655_; lean_object* v_idx_1656_; 
v_pos_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_pos_1655_);
v_idx_1656_ = lean_ctor_get(v_pos_1655_, 1);
lean_inc(v_idx_1656_);
v_idx_1629_ = v_idx_1651_;
v___y_1630_ = v___x_1654_;
v_pos_1631_ = v_pos_1655_;
v_idx_1632_ = v_idx_1656_;
goto v___jp_1628_;
}
}
else
{
lean_object* v_err_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_err_1657_ = lean_ctor_get(v___x_1654_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v___x_1654_, 0);
lean_dec(v_unused_1665_);
v___x_1659_ = v___x_1654_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_err_1657_);
lean_dec(v___x_1654_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
lean_inc_ref(v_pos_1650_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v_pos_1650_);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_pos_1650_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_err_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_inc(v_idx_1651_);
v_idx_1629_ = v_idx_1651_;
v___y_1630_ = v___x_1662_;
v_pos_1631_ = v_pos_1650_;
v_idx_1632_ = v_idx_1651_;
goto v___jp_1628_;
}
}
}
}
}
v___jp_1667_:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_nat_dec_eq(v_idx_1668_, v_idx_1671_);
lean_dec(v_idx_1668_);
if (v___x_1672_ == 0)
{
lean_dec(v_idx_1671_);
lean_dec_ref(v_pos_1670_);
return v___y_1669_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref(v___y_1669_);
v___x_1673_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112);
lean_inc_ref(v_pos_1670_);
v___x_1674_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1673_, v___f_1666_, v_pos_1670_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_dec_ref(v_pos_1670_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_dec(v_idx_1671_);
return v___x_1674_;
}
else
{
lean_object* v_pos_1675_; lean_object* v_idx_1676_; 
v_pos_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_pos_1675_);
v_idx_1676_ = lean_ctor_get(v_pos_1675_, 1);
lean_inc(v_idx_1676_);
v_idx_1648_ = v_idx_1671_;
v___y_1649_ = v___x_1674_;
v_pos_1650_ = v_pos_1675_;
v_idx_1651_ = v_idx_1676_;
goto v___jp_1647_;
}
}
else
{
lean_object* v_err_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_err_1677_ = lean_ctor_get(v___x_1674_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v___x_1674_, 0);
lean_dec(v_unused_1685_);
v___x_1679_ = v___x_1674_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_err_1677_);
lean_dec(v___x_1674_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
lean_inc_ref(v_pos_1670_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v_pos_1670_);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_pos_1670_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_err_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_inc(v_idx_1671_);
v_idx_1648_ = v_idx_1671_;
v___y_1649_ = v___x_1682_;
v_pos_1650_ = v_pos_1670_;
v_idx_1651_ = v_idx_1671_;
goto v___jp_1647_;
}
}
}
}
}
v___jp_1686_:
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_nat_dec_eq(v_idx_1687_, v_idx_1690_);
lean_dec(v_idx_1687_);
if (v___x_1691_ == 0)
{
lean_dec(v_idx_1690_);
lean_dec_ref(v_pos_1689_);
return v___y_1688_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec_ref(v___y_1688_);
v___x_1692_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115);
lean_inc_ref(v_pos_1689_);
v___x_1693_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1692_, v___f_1126_, v_pos_1689_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_dec_ref(v_pos_1689_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_dec(v_idx_1690_);
return v___x_1693_;
}
else
{
lean_object* v_pos_1694_; lean_object* v_idx_1695_; 
v_pos_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_pos_1694_);
v_idx_1695_ = lean_ctor_get(v_pos_1694_, 1);
lean_inc(v_idx_1695_);
v_idx_1668_ = v_idx_1690_;
v___y_1669_ = v___x_1693_;
v_pos_1670_ = v_pos_1694_;
v_idx_1671_ = v_idx_1695_;
goto v___jp_1667_;
}
}
else
{
lean_object* v_err_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_err_1696_ = lean_ctor_get(v___x_1693_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v___x_1693_, 0);
lean_dec(v_unused_1704_);
v___x_1698_ = v___x_1693_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_err_1696_);
lean_dec(v___x_1693_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
lean_inc_ref(v_pos_1689_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v_pos_1689_);
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1689_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_err_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_inc(v_idx_1690_);
v_idx_1668_ = v_idx_1690_;
v___y_1669_ = v___x_1701_;
v_pos_1670_ = v_pos_1689_;
v_idx_1671_ = v_idx_1690_;
goto v___jp_1667_;
}
}
}
}
}
v___jp_1706_:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_nat_dec_eq(v_idx_1707_, v_idx_1710_);
lean_dec(v_idx_1707_);
if (v___x_1711_ == 0)
{
lean_dec(v_idx_1710_);
lean_dec_ref(v_pos_1709_);
return v___y_1708_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec_ref(v___y_1708_);
v___x_1712_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119);
lean_inc_ref(v_pos_1709_);
v___x_1713_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1712_, v___f_1705_, v_pos_1709_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_dec_ref(v_pos_1709_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_dec(v_idx_1710_);
return v___x_1713_;
}
else
{
lean_object* v_pos_1714_; lean_object* v_idx_1715_; 
v_pos_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_pos_1714_);
v_idx_1715_ = lean_ctor_get(v_pos_1714_, 1);
lean_inc(v_idx_1715_);
v_idx_1687_ = v_idx_1710_;
v___y_1688_ = v___x_1713_;
v_pos_1689_ = v_pos_1714_;
v_idx_1690_ = v_idx_1715_;
goto v___jp_1686_;
}
}
else
{
lean_object* v_err_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v_err_1716_ = lean_ctor_get(v___x_1713_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v___x_1713_, 0);
lean_dec(v_unused_1724_);
v___x_1718_ = v___x_1713_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_err_1716_);
lean_dec(v___x_1713_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
lean_inc_ref(v_pos_1709_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v_pos_1709_);
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_pos_1709_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_err_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_inc(v_idx_1710_);
v_idx_1687_ = v_idx_1710_;
v___y_1688_ = v___x_1721_;
v_pos_1689_ = v_pos_1709_;
v_idx_1690_ = v_idx_1710_;
goto v___jp_1686_;
}
}
}
}
}
v___jp_1725_:
{
uint8_t v___x_1730_; 
v___x_1730_ = lean_nat_dec_eq(v_idx_1726_, v_idx_1729_);
lean_dec(v_idx_1726_);
if (v___x_1730_ == 0)
{
lean_dec(v_idx_1729_);
lean_dec_ref(v_pos_1728_);
return v___y_1727_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec_ref(v___y_1727_);
v___x_1731_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122);
lean_inc_ref(v_pos_1728_);
v___x_1732_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1731_, v___f_1125_, v_pos_1728_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_dec_ref(v_pos_1728_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_dec(v_idx_1729_);
return v___x_1732_;
}
else
{
lean_object* v_pos_1733_; lean_object* v_idx_1734_; 
v_pos_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_pos_1733_);
v_idx_1734_ = lean_ctor_get(v_pos_1733_, 1);
lean_inc(v_idx_1734_);
v_idx_1707_ = v_idx_1729_;
v___y_1708_ = v___x_1732_;
v_pos_1709_ = v_pos_1733_;
v_idx_1710_ = v_idx_1734_;
goto v___jp_1706_;
}
}
else
{
lean_object* v_err_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
v_err_1735_ = lean_ctor_get(v___x_1732_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v___x_1732_, 0);
lean_dec(v_unused_1743_);
v___x_1737_ = v___x_1732_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_err_1735_);
lean_dec(v___x_1732_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
lean_inc_ref(v_pos_1728_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v_pos_1728_);
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_pos_1728_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_err_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_inc(v_idx_1729_);
v_idx_1707_ = v_idx_1729_;
v___y_1708_ = v___x_1740_;
v_pos_1709_ = v_pos_1728_;
v_idx_1710_ = v_idx_1729_;
goto v___jp_1706_;
}
}
}
}
}
v___jp_1745_:
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_nat_dec_eq(v_idx_1746_, v_idx_1749_);
lean_dec(v_idx_1746_);
if (v___x_1750_ == 0)
{
lean_dec(v_idx_1749_);
lean_dec_ref(v_pos_1748_);
return v___y_1747_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec_ref(v___y_1747_);
v___x_1751_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126);
lean_inc_ref(v_pos_1748_);
v___x_1752_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1751_, v___f_1744_, v_pos_1748_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_dec_ref(v_pos_1748_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_dec(v_idx_1749_);
return v___x_1752_;
}
else
{
lean_object* v_pos_1753_; lean_object* v_idx_1754_; 
v_pos_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_pos_1753_);
v_idx_1754_ = lean_ctor_get(v_pos_1753_, 1);
lean_inc(v_idx_1754_);
v_idx_1726_ = v_idx_1749_;
v___y_1727_ = v___x_1752_;
v_pos_1728_ = v_pos_1753_;
v_idx_1729_ = v_idx_1754_;
goto v___jp_1725_;
}
}
else
{
lean_object* v_err_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
v_err_1755_ = lean_ctor_get(v___x_1752_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; 
v_unused_1763_ = lean_ctor_get(v___x_1752_, 0);
lean_dec(v_unused_1763_);
v___x_1757_ = v___x_1752_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_err_1755_);
lean_dec(v___x_1752_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
lean_inc_ref(v_pos_1748_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v_pos_1748_);
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_pos_1748_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_err_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_inc(v_idx_1749_);
v_idx_1726_ = v_idx_1749_;
v___y_1727_ = v___x_1760_;
v_pos_1728_ = v_pos_1748_;
v_idx_1729_ = v_idx_1749_;
goto v___jp_1725_;
}
}
}
}
}
v___jp_1764_:
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_nat_dec_eq(v_idx_1765_, v_idx_1768_);
lean_dec(v_idx_1765_);
if (v___x_1769_ == 0)
{
lean_dec(v_idx_1768_);
lean_dec_ref(v_pos_1767_);
return v___y_1766_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec_ref(v___y_1766_);
v___x_1770_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129);
lean_inc_ref(v_pos_1767_);
v___x_1771_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1770_, v___f_1124_, v_pos_1767_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_dec_ref(v_pos_1767_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_dec(v_idx_1768_);
return v___x_1771_;
}
else
{
lean_object* v_pos_1772_; lean_object* v_idx_1773_; 
v_pos_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_pos_1772_);
v_idx_1773_ = lean_ctor_get(v_pos_1772_, 1);
lean_inc(v_idx_1773_);
v_idx_1746_ = v_idx_1768_;
v___y_1747_ = v___x_1771_;
v_pos_1748_ = v_pos_1772_;
v_idx_1749_ = v_idx_1773_;
goto v___jp_1745_;
}
}
else
{
lean_object* v_err_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
v_err_1774_ = lean_ctor_get(v___x_1771_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1782_);
v___x_1776_ = v___x_1771_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_err_1774_);
lean_dec(v___x_1771_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
lean_inc_ref(v_pos_1767_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_pos_1767_);
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_pos_1767_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_err_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_inc(v_idx_1768_);
v_idx_1746_ = v_idx_1768_;
v___y_1747_ = v___x_1779_;
v_pos_1748_ = v_pos_1767_;
v_idx_1749_ = v_idx_1768_;
goto v___jp_1745_;
}
}
}
}
}
v___jp_1784_:
{
uint8_t v___x_1789_; 
v___x_1789_ = lean_nat_dec_eq(v_idx_1785_, v_idx_1788_);
lean_dec(v_idx_1785_);
if (v___x_1789_ == 0)
{
lean_dec(v_idx_1788_);
lean_dec_ref(v_pos_1787_);
return v___y_1786_;
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec_ref(v___y_1786_);
v___x_1790_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133);
lean_inc_ref(v_pos_1787_);
v___x_1791_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1790_, v___f_1783_, v_pos_1787_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_dec_ref(v_pos_1787_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_dec(v_idx_1788_);
return v___x_1791_;
}
else
{
lean_object* v_pos_1792_; lean_object* v_idx_1793_; 
v_pos_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_pos_1792_);
v_idx_1793_ = lean_ctor_get(v_pos_1792_, 1);
lean_inc(v_idx_1793_);
v_idx_1765_ = v_idx_1788_;
v___y_1766_ = v___x_1791_;
v_pos_1767_ = v_pos_1792_;
v_idx_1768_ = v_idx_1793_;
goto v___jp_1764_;
}
}
else
{
lean_object* v_err_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_err_1794_ = lean_ctor_get(v___x_1791_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v___x_1791_, 0);
lean_dec(v_unused_1802_);
v___x_1796_ = v___x_1791_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_err_1794_);
lean_dec(v___x_1791_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
lean_inc_ref(v_pos_1787_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v_pos_1787_);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_pos_1787_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_err_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_inc(v_idx_1788_);
v_idx_1765_ = v_idx_1788_;
v___y_1766_ = v___x_1799_;
v_pos_1767_ = v_pos_1787_;
v_idx_1768_ = v_idx_1788_;
goto v___jp_1764_;
}
}
}
}
}
v___jp_1803_:
{
uint8_t v___x_1808_; 
v___x_1808_ = lean_nat_dec_eq(v_idx_1804_, v_idx_1807_);
lean_dec(v_idx_1804_);
if (v___x_1808_ == 0)
{
lean_dec(v_idx_1807_);
lean_dec_ref(v_pos_1806_);
return v___y_1805_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec_ref(v___y_1805_);
v___x_1809_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136);
lean_inc_ref(v_pos_1806_);
v___x_1810_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1809_, v___f_1123_, v_pos_1806_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_dec_ref(v_pos_1806_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_dec(v_idx_1807_);
return v___x_1810_;
}
else
{
lean_object* v_pos_1811_; lean_object* v_idx_1812_; 
v_pos_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_pos_1811_);
v_idx_1812_ = lean_ctor_get(v_pos_1811_, 1);
lean_inc(v_idx_1812_);
v_idx_1785_ = v_idx_1807_;
v___y_1786_ = v___x_1810_;
v_pos_1787_ = v_pos_1811_;
v_idx_1788_ = v_idx_1812_;
goto v___jp_1784_;
}
}
else
{
lean_object* v_err_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_err_1813_ = lean_ctor_get(v___x_1810_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1810_, 0);
lean_dec(v_unused_1821_);
v___x_1815_ = v___x_1810_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_err_1813_);
lean_dec(v___x_1810_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
lean_inc_ref(v_pos_1806_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v_pos_1806_);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_pos_1806_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_err_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_inc(v_idx_1807_);
v_idx_1785_ = v_idx_1807_;
v___y_1786_ = v___x_1818_;
v_pos_1787_ = v_pos_1806_;
v_idx_1788_ = v_idx_1807_;
goto v___jp_1784_;
}
}
}
}
}
v___jp_1823_:
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_nat_dec_eq(v_idx_1824_, v_idx_1827_);
lean_dec(v_idx_1824_);
if (v___x_1828_ == 0)
{
lean_dec(v_idx_1827_);
lean_dec_ref(v_pos_1826_);
return v___y_1825_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v___y_1825_);
v___x_1829_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140);
lean_inc_ref(v_pos_1826_);
v___x_1830_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1829_, v___f_1822_, v_pos_1826_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_dec_ref(v_pos_1826_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_dec(v_idx_1827_);
return v___x_1830_;
}
else
{
lean_object* v_pos_1831_; lean_object* v_idx_1832_; 
v_pos_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_pos_1831_);
v_idx_1832_ = lean_ctor_get(v_pos_1831_, 1);
lean_inc(v_idx_1832_);
v_idx_1804_ = v_idx_1827_;
v___y_1805_ = v___x_1830_;
v_pos_1806_ = v_pos_1831_;
v_idx_1807_ = v_idx_1832_;
goto v___jp_1803_;
}
}
else
{
lean_object* v_err_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
v_err_1833_ = lean_ctor_get(v___x_1830_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; 
v_unused_1841_ = lean_ctor_get(v___x_1830_, 0);
lean_dec(v_unused_1841_);
v___x_1835_ = v___x_1830_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_err_1833_);
lean_dec(v___x_1830_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
lean_inc_ref(v_pos_1826_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v_pos_1826_);
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_pos_1826_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_err_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_inc(v_idx_1827_);
v_idx_1804_ = v_idx_1827_;
v___y_1805_ = v___x_1838_;
v_pos_1806_ = v_pos_1826_;
v_idx_1807_ = v_idx_1827_;
goto v___jp_1803_;
}
}
}
}
}
v___jp_1842_:
{
uint8_t v___x_1847_; 
v___x_1847_ = lean_nat_dec_eq(v_idx_1843_, v_idx_1846_);
lean_dec(v_idx_1843_);
if (v___x_1847_ == 0)
{
lean_dec(v_idx_1846_);
lean_dec_ref(v_pos_1845_);
return v___y_1844_;
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec_ref(v___y_1844_);
v___x_1848_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143);
lean_inc_ref(v_pos_1845_);
v___x_1849_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1848_, v___f_1122_, v_pos_1845_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_dec_ref(v_pos_1845_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_dec(v_idx_1846_);
return v___x_1849_;
}
else
{
lean_object* v_pos_1850_; lean_object* v_idx_1851_; 
v_pos_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_pos_1850_);
v_idx_1851_ = lean_ctor_get(v_pos_1850_, 1);
lean_inc(v_idx_1851_);
v_idx_1824_ = v_idx_1846_;
v___y_1825_ = v___x_1849_;
v_pos_1826_ = v_pos_1850_;
v_idx_1827_ = v_idx_1851_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_err_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_err_1852_ = lean_ctor_get(v___x_1849_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1860_);
v___x_1854_ = v___x_1849_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_err_1852_);
lean_dec(v___x_1849_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
lean_inc_ref(v_pos_1845_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_pos_1845_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_pos_1845_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_err_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_inc(v_idx_1846_);
v_idx_1824_ = v_idx_1846_;
v___y_1825_ = v___x_1857_;
v_pos_1826_ = v_pos_1845_;
v_idx_1827_ = v_idx_1846_;
goto v___jp_1823_;
}
}
}
}
}
v___jp_1862_:
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_nat_dec_eq(v_idx_1863_, v_idx_1866_);
lean_dec(v_idx_1863_);
if (v___x_1867_ == 0)
{
lean_dec(v_idx_1866_);
lean_dec_ref(v_pos_1865_);
return v___y_1864_;
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v___y_1864_);
v___x_1868_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147);
lean_inc_ref(v_pos_1865_);
v___x_1869_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1868_, v___f_1861_, v_pos_1865_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_dec_ref(v_pos_1865_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_dec(v_idx_1866_);
return v___x_1869_;
}
else
{
lean_object* v_pos_1870_; lean_object* v_idx_1871_; 
v_pos_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_pos_1870_);
v_idx_1871_ = lean_ctor_get(v_pos_1870_, 1);
lean_inc(v_idx_1871_);
v_idx_1843_ = v_idx_1866_;
v___y_1844_ = v___x_1869_;
v_pos_1845_ = v_pos_1870_;
v_idx_1846_ = v_idx_1871_;
goto v___jp_1842_;
}
}
else
{
lean_object* v_err_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_err_1872_ = lean_ctor_get(v___x_1869_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; 
v_unused_1880_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1880_);
v___x_1874_ = v___x_1869_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_err_1872_);
lean_dec(v___x_1869_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
lean_inc_ref(v_pos_1865_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v_pos_1865_);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_pos_1865_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_err_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_inc(v_idx_1866_);
v_idx_1843_ = v_idx_1866_;
v___y_1844_ = v___x_1877_;
v_pos_1845_ = v_pos_1865_;
v_idx_1846_ = v_idx_1866_;
goto v___jp_1842_;
}
}
}
}
}
v___jp_1881_:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_nat_dec_eq(v_idx_1882_, v_idx_1885_);
lean_dec(v_idx_1882_);
if (v___x_1886_ == 0)
{
lean_dec(v_idx_1885_);
lean_dec_ref(v_pos_1884_);
return v___y_1883_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec_ref(v___y_1883_);
v___x_1887_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150);
lean_inc_ref(v_pos_1884_);
v___x_1888_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1887_, v___f_1121_, v_pos_1884_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_dec_ref(v_pos_1884_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_dec(v_idx_1885_);
return v___x_1888_;
}
else
{
lean_object* v_pos_1889_; lean_object* v_idx_1890_; 
v_pos_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_pos_1889_);
v_idx_1890_ = lean_ctor_get(v_pos_1889_, 1);
lean_inc(v_idx_1890_);
v_idx_1863_ = v_idx_1885_;
v___y_1864_ = v___x_1888_;
v_pos_1865_ = v_pos_1889_;
v_idx_1866_ = v_idx_1890_;
goto v___jp_1862_;
}
}
else
{
lean_object* v_err_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_err_1891_ = lean_ctor_get(v___x_1888_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v___x_1888_, 0);
lean_dec(v_unused_1899_);
v___x_1893_ = v___x_1888_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_err_1891_);
lean_dec(v___x_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
lean_inc_ref(v_pos_1884_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_pos_1884_);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_pos_1884_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_err_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_inc(v_idx_1885_);
v_idx_1863_ = v_idx_1885_;
v___y_1864_ = v___x_1896_;
v_pos_1865_ = v_pos_1884_;
v_idx_1866_ = v_idx_1885_;
goto v___jp_1862_;
}
}
}
}
}
v___jp_1901_:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_nat_dec_eq(v_idx_1902_, v_idx_1905_);
lean_dec(v_idx_1902_);
if (v___x_1906_ == 0)
{
lean_dec(v_idx_1905_);
lean_dec_ref(v_pos_1904_);
return v___y_1903_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_dec_ref(v___y_1903_);
v___x_1907_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154);
lean_inc_ref(v_pos_1904_);
v___x_1908_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1907_, v___f_1900_, v_pos_1904_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_dec_ref(v_pos_1904_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_dec(v_idx_1905_);
return v___x_1908_;
}
else
{
lean_object* v_pos_1909_; lean_object* v_idx_1910_; 
v_pos_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_pos_1909_);
v_idx_1910_ = lean_ctor_get(v_pos_1909_, 1);
lean_inc(v_idx_1910_);
v_idx_1882_ = v_idx_1905_;
v___y_1883_ = v___x_1908_;
v_pos_1884_ = v_pos_1909_;
v_idx_1885_ = v_idx_1910_;
goto v___jp_1881_;
}
}
else
{
lean_object* v_err_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_err_1911_ = lean_ctor_get(v___x_1908_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1908_, 0);
lean_dec(v_unused_1919_);
v___x_1913_ = v___x_1908_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_err_1911_);
lean_dec(v___x_1908_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
lean_inc_ref(v_pos_1904_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v_pos_1904_);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_pos_1904_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_err_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_inc(v_idx_1905_);
v_idx_1882_ = v_idx_1905_;
v___y_1883_ = v___x_1916_;
v_pos_1884_ = v_pos_1904_;
v_idx_1885_ = v_idx_1905_;
goto v___jp_1881_;
}
}
}
}
}
v___jp_1920_:
{
lean_object* v_idx_1923_; lean_object* v_idx_1924_; uint8_t v___x_1925_; 
v_idx_1923_ = lean_ctor_get(v_a_1119_, 1);
lean_inc(v_idx_1923_);
lean_dec_ref(v_a_1119_);
v_idx_1924_ = lean_ctor_get(v_pos_1922_, 1);
lean_inc(v_idx_1924_);
v___x_1925_ = lean_nat_dec_eq(v_idx_1923_, v_idx_1924_);
lean_dec(v_idx_1923_);
if (v___x_1925_ == 0)
{
lean_dec(v_idx_1924_);
lean_dec_ref(v_pos_1922_);
return v___y_1921_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec_ref(v___y_1921_);
v___x_1926_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157);
lean_inc_ref(v_pos_1922_);
v___x_1927_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1926_, v___f_1120_, v_pos_1922_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_dec_ref(v_pos_1922_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_dec(v_idx_1924_);
return v___x_1927_;
}
else
{
lean_object* v_pos_1928_; lean_object* v_idx_1929_; 
v_pos_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_pos_1928_);
v_idx_1929_ = lean_ctor_get(v_pos_1928_, 1);
lean_inc(v_idx_1929_);
v_idx_1902_ = v_idx_1924_;
v___y_1903_ = v___x_1927_;
v_pos_1904_ = v_pos_1928_;
v_idx_1905_ = v_idx_1929_;
goto v___jp_1901_;
}
}
else
{
lean_object* v_err_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_err_1930_ = lean_ctor_get(v___x_1927_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v___x_1927_, 0);
lean_dec(v_unused_1938_);
v___x_1932_ = v___x_1927_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_err_1930_);
lean_dec(v___x_1927_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
lean_inc_ref(v_pos_1922_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v_pos_1922_);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_pos_1922_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_err_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_inc(v_idx_1924_);
v_idx_1902_ = v_idx_1924_;
v___y_1903_ = v___x_1935_;
v_pos_1904_ = v_pos_1922_;
v_idx_1905_ = v_idx_1924_;
goto v___jp_1901_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1952_){
_start:
{
uint8_t v___x_1953_; uint8_t v___x_1954_; 
v___x_1953_ = 32;
v___x_1954_ = lean_uint8_dec_eq(v_b_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
uint8_t v___x_1955_; 
v___x_1955_ = 1;
return v___x_1955_;
}
else
{
uint8_t v___x_1956_; 
v___x_1956_ = 0;
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1957_){
_start:
{
uint8_t v_b_boxed_1958_; uint8_t v_res_1959_; lean_object* v_r_1960_; 
v_b_boxed_1958_ = lean_unbox(v_b_1957_);
v_res_1959_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1958_);
v_r_1960_ = lean_box(v_res_1959_);
return v_r_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v_maxUriLength_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_snd_1976_; lean_object* v_snd_1977_; uint8_t v___x_1978_; 
v_maxUriLength_1972_ = lean_ctor_get(v_limits_1965_, 4);
v___f_1973_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_1974_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1966_);
v___x_1975_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1973_, v_maxUriLength_1972_, v___x_1974_, v_a_1966_);
v_snd_1976_ = lean_ctor_get(v___x_1975_, 1);
lean_inc(v_snd_1976_);
v_snd_1977_ = lean_ctor_get(v_snd_1976_, 1);
v___x_1978_ = lean_unbox(v_snd_1977_);
if (v___x_1978_ == 0)
{
lean_object* v_fst_1979_; lean_object* v_fst_1980_; lean_object* v_array_1981_; lean_object* v_idx_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2009_; 
v_fst_1979_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_fst_1979_);
lean_dec_ref(v___x_1975_);
v_fst_1980_ = lean_ctor_get(v_snd_1976_, 0);
lean_inc(v_fst_1980_);
lean_dec(v_snd_1976_);
v_array_1981_ = lean_ctor_get(v_a_1966_, 0);
v_idx_1982_ = lean_ctor_get(v_a_1966_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_a_1966_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1984_ = v_a_1966_;
v_isShared_1985_ = v_isSharedCheck_2009_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_idx_1982_);
lean_inc(v_array_1981_);
lean_dec(v_a_1966_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2009_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_lower_1987_; lean_object* v_upper_1988_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___y_2006_; uint8_t v___x_2008_; 
v___x_2003_ = lean_nat_add(v_idx_1982_, v_fst_1979_);
lean_dec(v_fst_1979_);
v___x_2004_ = lean_byte_array_size(v_array_1981_);
v___x_2008_ = lean_nat_dec_le(v_idx_1982_, v___x_1974_);
if (v___x_2008_ == 0)
{
v___y_2006_ = v_idx_1982_;
goto v___jp_2005_;
}
else
{
lean_dec(v_idx_1982_);
v___y_2006_ = v___x_1974_;
goto v___jp_2005_;
}
v___jp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1989_ = l_ByteArray_toByteSlice(v_array_1981_, v_lower_1987_, v_upper_1988_);
v___x_1990_ = l_ByteSlice_size(v___x_1989_);
v___x_1991_ = lean_nat_dec_eq(v___x_1990_, v_maxUriLength_1972_);
lean_dec(v___x_1990_);
if (v___x_1991_ == 0)
{
lean_del_object(v___x_1984_);
v___y_1968_ = v___x_1989_;
v___y_1969_ = v_fst_1980_;
goto v___jp_1967_;
}
else
{
lean_object* v_array_1992_; lean_object* v_idx_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_array_1992_ = lean_ctor_get(v_fst_1980_, 0);
v_idx_1993_ = lean_ctor_get(v_fst_1980_, 1);
v___x_1994_ = lean_byte_array_size(v_array_1992_);
v___x_1995_ = lean_nat_dec_lt(v_idx_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_del_object(v___x_1984_);
v___y_1968_ = v___x_1989_;
v___y_1969_ = v_fst_1980_;
goto v___jp_1967_;
}
else
{
uint8_t v___x_1996_; uint8_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_byte_array_fget(v_array_1992_, v_idx_1993_);
v___x_1997_ = 32;
v___x_1998_ = lean_uint8_dec_eq(v___x_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_dec_ref(v___x_1989_);
v___x_1999_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 1);
lean_ctor_set(v___x_1984_, 1, v___x_1999_);
lean_ctor_set(v___x_1984_, 0, v_fst_1980_);
v___x_2001_ = v___x_1984_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_fst_1980_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_del_object(v___x_1984_);
v___y_1968_ = v___x_1989_;
v___y_1969_ = v_fst_1980_;
goto v___jp_1967_;
}
}
}
}
v___jp_2005_:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_nat_dec_le(v___x_2003_, v___x_2004_);
if (v___x_2007_ == 0)
{
lean_dec(v___x_2003_);
v_lower_1987_ = v___y_2006_;
v_upper_1988_ = v___x_2004_;
goto v___jp_1986_;
}
else
{
v_lower_1987_ = v___y_2006_;
v_upper_1988_ = v___x_2003_;
goto v___jp_1986_;
}
}
}
}
else
{
lean_object* v_fst_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v___x_1975_);
lean_dec_ref(v_a_1966_);
v_fst_2010_ = lean_ctor_get(v_snd_1976_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_snd_1976_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v_snd_1976_, 1);
lean_dec(v_unused_2019_);
v___x_2012_ = v_snd_1976_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_fst_2010_);
lean_dec(v_snd_1976_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(0);
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 1);
lean_ctor_set(v___x_2012_, 1, v___x_2014_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_fst_2010_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
v___jp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = l_ByteSlice_toByteArray(v___y_1968_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___y_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
return v___x_1971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2020_, v_a_2021_);
lean_dec_ref(v_limits_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_pos_2029_; lean_object* v_array_2030_; lean_object* v_idx_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_pos_2029_ = lean_ctor_get(v___x_2028_, 0);
v_array_2030_ = lean_ctor_get(v_pos_2029_, 0);
v_idx_2031_ = lean_ctor_get(v_pos_2029_, 1);
v___x_2032_ = lean_byte_array_size(v_array_2030_);
v___x_2033_ = lean_nat_dec_lt(v_idx_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
return v___x_2028_;
}
else
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2041_; 
lean_inc(v_pos_2029_);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; lean_object* v_unused_2043_; 
v_unused_2042_ = lean_ctor_get(v___x_2028_, 1);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v___x_2028_, 0);
lean_dec(v_unused_2043_);
v___x_2035_ = v___x_2028_;
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v___x_2028_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 1);
lean_ctor_set(v___x_2035_, 1, v___x_2037_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_pos_2029_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___y_2057_; lean_object* v_pos_2058_; lean_object* v_res_2059_; lean_object* v_pos_2063_; lean_object* v_res_2064_; lean_object* v___x_2103_; 
v___x_2103_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_pos_2104_; lean_object* v_res_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2135_; 
v_pos_2104_ = lean_ctor_get(v___x_2103_, 0);
v_res_2105_ = lean_ctor_get(v___x_2103_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2107_ = v___x_2103_;
v_isShared_2108_ = v_isSharedCheck_2135_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_res_2105_);
lean_inc(v_pos_2104_);
lean_dec(v___x_2103_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2135_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v_array_2109_; lean_object* v_idx_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_array_2109_ = lean_ctor_get(v_pos_2104_, 0);
v_idx_2110_ = lean_ctor_get(v_pos_2104_, 1);
v___x_2111_ = lean_byte_array_size(v_array_2109_);
v___x_2112_ = lean_nat_dec_lt(v_idx_2110_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2115_; 
lean_dec(v_res_2105_);
v___x_2113_ = lean_box(0);
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 1);
lean_ctor_set(v___x_2107_, 1, v___x_2113_);
v___x_2115_ = v___x_2107_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_pos_2104_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
else
{
uint8_t v___x_2117_; uint8_t v_got_2118_; uint8_t v___x_2119_; 
v___x_2117_ = 32;
v_got_2118_ = lean_byte_array_fget(v_array_2109_, v_idx_2110_);
v___x_2119_ = lean_uint8_dec_eq(v_got_2118_, v___x_2117_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_dec(v_res_2105_);
v___x_2120_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 1);
lean_ctor_set(v___x_2107_, 1, v___x_2120_);
v___x_2122_ = v___x_2107_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_pos_2104_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
else
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2132_; 
lean_inc(v_idx_2110_);
lean_inc_ref(v_array_2109_);
lean_del_object(v___x_2107_);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_pos_2104_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; lean_object* v_unused_2134_; 
v_unused_2133_ = lean_ctor_get(v_pos_2104_, 1);
lean_dec(v_unused_2133_);
v_unused_2134_ = lean_ctor_get(v_pos_2104_, 0);
lean_dec(v_unused_2134_);
v___x_2125_ = v_pos_2104_;
v_isShared_2126_ = v_isSharedCheck_2132_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v_pos_2104_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2132_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = lean_nat_add(v_idx_2110_, v___x_2127_);
lean_dec(v_idx_2110_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 1, v___x_2128_);
v___x_2130_ = v___x_2125_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_array_2109_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
v_pos_2063_ = v___x_2130_;
v_res_2064_ = v_res_2105_;
goto v___jp_2062_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_pos_2136_; lean_object* v_res_2137_; 
v_pos_2136_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_pos_2136_);
v_res_2137_ = lean_ctor_get(v___x_2103_, 1);
lean_inc(v_res_2137_);
lean_dec_ref_known(v___x_2103_, 2);
v_pos_2063_ = v_pos_2136_;
v_res_2064_ = v_res_2137_;
goto v___jp_2062_;
}
else
{
lean_object* v_pos_2138_; lean_object* v_err_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
v_pos_2138_ = lean_ctor_get(v___x_2103_, 0);
v_err_2139_ = lean_ctor_get(v___x_2103_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2103_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_err_2139_);
lean_inc(v_pos_2138_);
lean_dec(v___x_2103_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_pos_2138_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_err_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
v___jp_2056_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___y_2057_);
lean_ctor_set(v___x_2060_, 1, v_res_2059_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v_pos_2058_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
return v___x_2061_;
}
v___jp_2062_:
{
lean_object* v___f_2065_; lean_object* v___x_2066_; 
v___f_2065_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_2066_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_2065_, v_res_2064_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 1);
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2073_, 0, v_pos_2063_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
return v___x_2073_;
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2077_; 
v_a_2076_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2077_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_pos_2063_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_pos_2078_; lean_object* v_res_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_pos_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_pos_2078_);
v_res_2079_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_res_2079_);
lean_dec_ref_known(v___x_2077_, 2);
v___x_2080_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2081_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2080_, v_pos_2078_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_pos_2082_; 
v_pos_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_pos_2082_);
lean_dec_ref_known(v___x_2081_, 2);
v___y_2057_ = v_a_2076_;
v_pos_2058_ = v_pos_2082_;
v_res_2059_ = v_res_2079_;
goto v___jp_2056_;
}
else
{
lean_object* v_pos_2083_; lean_object* v_err_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_res_2079_);
lean_dec(v_a_2076_);
v_pos_2083_ = lean_ctor_get(v___x_2081_, 0);
v_err_2084_ = lean_ctor_get(v___x_2081_, 1);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2081_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_err_2084_);
lean_inc(v_pos_2083_);
lean_dec(v___x_2081_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_pos_2083_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_err_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_pos_2092_; lean_object* v_res_2093_; 
v_pos_2092_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_pos_2092_);
v_res_2093_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_res_2093_);
lean_dec_ref_known(v___x_2077_, 2);
v___y_2057_ = v_a_2076_;
v_pos_2058_ = v_pos_2092_;
v_res_2059_ = v_res_2093_;
goto v___jp_2056_;
}
else
{
lean_object* v_pos_2094_; lean_object* v_err_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_2076_);
v_pos_2094_ = lean_ctor_get(v___x_2077_, 0);
v_err_2095_ = lean_ctor_get(v___x_2077_, 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2077_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_err_2095_);
lean_inc(v_pos_2094_);
lean_dec(v___x_2077_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_pos_2094_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_err_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2147_, v_a_2148_);
lean_dec_ref(v_limits_2147_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v___y_2156_; uint8_t v___y_2160_; lean_object* v___y_2161_; uint8_t v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; uint8_t v___y_2165_; lean_object* v_pos_2177_; uint8_t v_res_2178_; lean_object* v___x_2198_; 
v___x_2198_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_pos_2199_; lean_object* v___x_2200_; 
v_pos_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_pos_2199_);
lean_dec_ref_known(v___x_2198_, 2);
v___x_2200_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2199_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_pos_2201_; lean_object* v_res_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2233_; 
v_pos_2201_ = lean_ctor_get(v___x_2200_, 0);
v_res_2202_ = lean_ctor_get(v___x_2200_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2204_ = v___x_2200_;
v_isShared_2205_ = v_isSharedCheck_2233_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_res_2202_);
lean_inc(v_pos_2201_);
lean_dec(v___x_2200_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2233_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_array_2206_; lean_object* v_idx_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v_array_2206_ = lean_ctor_get(v_pos_2201_, 0);
v_idx_2207_ = lean_ctor_get(v_pos_2201_, 1);
v___x_2208_ = lean_byte_array_size(v_array_2206_);
v___x_2209_ = lean_nat_dec_lt(v_idx_2207_, v___x_2208_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
lean_dec(v_res_2202_);
v___x_2210_ = lean_box(0);
if (v_isShared_2205_ == 0)
{
lean_ctor_set_tag(v___x_2204_, 1);
lean_ctor_set(v___x_2204_, 1, v___x_2210_);
v___x_2212_ = v___x_2204_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_pos_2201_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
else
{
uint8_t v___x_2214_; uint8_t v_got_2215_; uint8_t v___x_2216_; 
v___x_2214_ = 32;
v_got_2215_ = lean_byte_array_fget(v_array_2206_, v_idx_2207_);
v___x_2216_ = lean_uint8_dec_eq(v_got_2215_, v___x_2214_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
lean_dec(v_res_2202_);
v___x_2217_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2205_ == 0)
{
lean_ctor_set_tag(v___x_2204_, 1);
lean_ctor_set(v___x_2204_, 1, v___x_2217_);
v___x_2219_ = v___x_2204_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_pos_2201_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
else
{
lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2230_; 
lean_inc(v_idx_2207_);
lean_inc_ref(v_array_2206_);
lean_del_object(v___x_2204_);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_pos_2201_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2231_ = lean_ctor_get(v_pos_2201_, 1);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_pos_2201_, 0);
lean_dec(v_unused_2232_);
v___x_2222_ = v_pos_2201_;
v_isShared_2223_ = v_isSharedCheck_2230_;
goto v_resetjp_2221_;
}
else
{
lean_dec(v_pos_2201_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2230_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = lean_unsigned_to_nat(1u);
v___x_2225_ = lean_nat_add(v_idx_2207_, v___x_2224_);
lean_dec(v_idx_2207_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v___x_2225_);
v___x_2227_ = v___x_2222_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_array_2206_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_unbox(v_res_2202_);
lean_dec(v_res_2202_);
v_pos_2177_ = v___x_2227_;
v_res_2178_ = v___x_2228_;
goto v___jp_2176_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_pos_2234_; lean_object* v_res_2235_; uint8_t v___x_2236_; 
v_pos_2234_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_pos_2234_);
v_res_2235_ = lean_ctor_get(v___x_2200_, 1);
lean_inc(v_res_2235_);
lean_dec_ref_known(v___x_2200_, 2);
v___x_2236_ = lean_unbox(v_res_2235_);
lean_dec(v_res_2235_);
v_pos_2177_ = v_pos_2234_;
v_res_2178_ = v___x_2236_;
goto v___jp_2176_;
}
else
{
lean_object* v_pos_2237_; lean_object* v_err_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_pos_2237_ = lean_ctor_get(v___x_2200_, 0);
v_err_2238_ = lean_ctor_get(v___x_2200_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2200_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_err_2238_);
lean_inc(v_pos_2237_);
lean_dec(v___x_2200_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_pos_2237_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_err_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
else
{
lean_object* v_pos_2246_; lean_object* v_err_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_pos_2246_ = lean_ctor_get(v___x_2198_, 0);
v_err_2247_ = lean_ctor_get(v___x_2198_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2198_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_err_2247_);
lean_inc(v_pos_2246_);
lean_dec(v___x_2198_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_pos_2246_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_err_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___y_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
return v___x_2158_;
}
v___jp_2159_:
{
if (v___y_2165_ == 0)
{
if (v___y_2162_ == 0)
{
lean_dec(v___y_2163_);
lean_dec(v___y_2161_);
v___y_2156_ = v___y_2164_;
goto v___jp_2155_;
}
else
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_nat_dec_eq(v___y_2163_, v___x_2166_);
lean_dec(v___y_2163_);
if (v___x_2167_ == 0)
{
lean_dec(v___y_2161_);
v___y_2156_ = v___y_2164_;
goto v___jp_2155_;
}
else
{
uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2168_ = 0;
v___x_2169_ = l_Std_Http_Headers_empty;
v___x_2170_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2170_, 0, v___y_2161_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*2, v___y_2160_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*2 + 1, v___x_2168_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___y_2164_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
return v___x_2171_;
}
}
}
else
{
uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec(v___y_2163_);
v___x_2172_ = 1;
v___x_2173_ = l_Std_Http_Headers_empty;
v___x_2174_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2174_, 0, v___y_2161_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*2, v___y_2160_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*2 + 1, v___x_2172_);
v___x_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___y_2164_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
return v___x_2175_;
}
}
v___jp_2176_:
{
lean_object* v___x_2179_; 
v___x_2179_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2153_, v_pos_2177_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_res_2180_; lean_object* v_snd_2181_; lean_object* v_pos_2182_; lean_object* v_fst_2183_; lean_object* v_fst_2184_; lean_object* v_snd_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_res_2180_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_res_2180_);
v_snd_2181_ = lean_ctor_get(v_res_2180_, 1);
lean_inc(v_snd_2181_);
v_pos_2182_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_pos_2182_);
lean_dec_ref_known(v___x_2179_, 2);
v_fst_2183_ = lean_ctor_get(v_res_2180_, 0);
lean_inc(v_fst_2183_);
lean_dec(v_res_2180_);
v_fst_2184_ = lean_ctor_get(v_snd_2181_, 0);
lean_inc(v_fst_2184_);
v_snd_2185_ = lean_ctor_get(v_snd_2181_, 1);
lean_inc(v_snd_2185_);
lean_dec(v_snd_2181_);
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_dec_eq(v_fst_2184_, v___x_2186_);
lean_dec(v_fst_2184_);
if (v___x_2187_ == 0)
{
v___y_2160_ = v_res_2178_;
v___y_2161_ = v_fst_2183_;
v___y_2162_ = v___x_2187_;
v___y_2163_ = v_snd_2185_;
v___y_2164_ = v_pos_2182_;
v___y_2165_ = v___x_2187_;
goto v___jp_2159_;
}
else
{
uint8_t v___x_2188_; 
v___x_2188_ = lean_nat_dec_eq(v_snd_2185_, v___x_2186_);
v___y_2160_ = v_res_2178_;
v___y_2161_ = v_fst_2183_;
v___y_2162_ = v___x_2187_;
v___y_2163_ = v_snd_2185_;
v___y_2164_ = v_pos_2182_;
v___y_2165_ = v___x_2188_;
goto v___jp_2159_;
}
}
else
{
lean_object* v_pos_2189_; lean_object* v_err_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_pos_2189_ = lean_ctor_get(v___x_2179_, 0);
v_err_2190_ = lean_ctor_get(v___x_2179_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2179_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_err_2190_);
lean_inc(v_pos_2189_);
lean_dec(v___x_2179_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_pos_2189_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_err_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_2255_, v_a_2256_);
lean_dec_ref(v_limits_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_pos_2261_; uint8_t v_res_2262_; lean_object* v___x_2304_; 
v___x_2304_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2258_, v_a_2259_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_pos_2305_; lean_object* v___x_2306_; 
v_pos_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_pos_2305_);
lean_dec_ref_known(v___x_2304_, 2);
v___x_2306_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2305_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_pos_2307_; lean_object* v_res_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2339_; 
v_pos_2307_ = lean_ctor_get(v___x_2306_, 0);
v_res_2308_ = lean_ctor_get(v___x_2306_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2310_ = v___x_2306_;
v_isShared_2311_ = v_isSharedCheck_2339_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_res_2308_);
lean_inc(v_pos_2307_);
lean_dec(v___x_2306_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2339_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_array_2312_; lean_object* v_idx_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_array_2312_ = lean_ctor_get(v_pos_2307_, 0);
v_idx_2313_ = lean_ctor_get(v_pos_2307_, 1);
v___x_2314_ = lean_byte_array_size(v_array_2312_);
v___x_2315_ = lean_nat_dec_lt(v_idx_2313_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_dec(v_res_2308_);
v___x_2316_ = lean_box(0);
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 1);
lean_ctor_set(v___x_2310_, 1, v___x_2316_);
v___x_2318_ = v___x_2310_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_pos_2307_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
else
{
uint8_t v___x_2320_; uint8_t v_got_2321_; uint8_t v___x_2322_; 
v___x_2320_ = 32;
v_got_2321_ = lean_byte_array_fget(v_array_2312_, v_idx_2313_);
v___x_2322_ = lean_uint8_dec_eq(v_got_2321_, v___x_2320_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
lean_dec(v_res_2308_);
v___x_2323_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 1);
lean_ctor_set(v___x_2310_, 1, v___x_2323_);
v___x_2325_ = v___x_2310_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_pos_2307_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
else
{
lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2336_; 
lean_inc(v_idx_2313_);
lean_inc_ref(v_array_2312_);
lean_del_object(v___x_2310_);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_pos_2307_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; lean_object* v_unused_2338_; 
v_unused_2337_ = lean_ctor_get(v_pos_2307_, 1);
lean_dec(v_unused_2337_);
v_unused_2338_ = lean_ctor_get(v_pos_2307_, 0);
lean_dec(v_unused_2338_);
v___x_2328_ = v_pos_2307_;
v_isShared_2329_ = v_isSharedCheck_2336_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v_pos_2307_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2336_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v_idx_2313_, v___x_2330_);
lean_dec(v_idx_2313_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_array_2312_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_unbox(v_res_2308_);
lean_dec(v_res_2308_);
v_pos_2261_ = v___x_2333_;
v_res_2262_ = v___x_2334_;
goto v___jp_2260_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_pos_2340_; lean_object* v_res_2341_; uint8_t v___x_2342_; 
v_pos_2340_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_pos_2340_);
v_res_2341_ = lean_ctor_get(v___x_2306_, 1);
lean_inc(v_res_2341_);
lean_dec_ref_known(v___x_2306_, 2);
v___x_2342_ = lean_unbox(v_res_2341_);
lean_dec(v_res_2341_);
v_pos_2261_ = v_pos_2340_;
v_res_2262_ = v___x_2342_;
goto v___jp_2260_;
}
else
{
lean_object* v_pos_2343_; lean_object* v_err_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_pos_2343_ = lean_ctor_get(v___x_2306_, 0);
v_err_2344_ = lean_ctor_get(v___x_2306_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2306_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_err_2344_);
lean_inc(v_pos_2343_);
lean_dec(v___x_2306_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_pos_2343_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_err_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
else
{
lean_object* v_pos_2352_; lean_object* v_err_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_pos_2352_ = lean_ctor_get(v___x_2304_, 0);
v_err_2353_ = lean_ctor_get(v___x_2304_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2304_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_err_2353_);
lean_inc(v_pos_2352_);
lean_dec(v___x_2304_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_pos_2352_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_err_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
v___jp_2260_:
{
lean_object* v___x_2263_; 
v___x_2263_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2258_, v_pos_2261_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_res_2264_; lean_object* v_snd_2265_; lean_object* v_pos_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2293_; 
v_res_2264_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_res_2264_);
v_snd_2265_ = lean_ctor_get(v_res_2264_, 1);
lean_inc(v_snd_2265_);
v_pos_2266_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; 
v_unused_2294_ = lean_ctor_get(v___x_2263_, 1);
lean_dec(v_unused_2294_);
v___x_2268_ = v___x_2263_;
v_isShared_2269_ = v_isSharedCheck_2293_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_pos_2266_);
lean_dec(v___x_2263_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2293_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v_fst_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2291_; 
v_fst_2270_ = lean_ctor_get(v_res_2264_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_res_2264_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v_res_2264_, 1);
lean_dec(v_unused_2292_);
v___x_2272_ = v_res_2264_;
v_isShared_2273_ = v_isSharedCheck_2291_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_fst_2270_);
lean_dec(v_res_2264_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2291_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_fst_2274_; lean_object* v_snd_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2290_; 
v_fst_2274_ = lean_ctor_get(v_snd_2265_, 0);
v_snd_2275_ = lean_ctor_get(v_snd_2265_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_snd_2265_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2277_ = v_snd_2265_;
v_isShared_2278_ = v_isSharedCheck_2290_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_snd_2275_);
lean_inc(v_fst_2274_);
lean_dec(v_snd_2265_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2290_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2279_ = l_Std_Http_Version_ofNumber_x3f(v_fst_2274_, v_snd_2275_);
lean_dec(v_snd_2275_);
lean_dec(v_fst_2274_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 1, v___x_2279_);
lean_ctor_set(v___x_2277_, 0, v_fst_2270_);
v___x_2281_ = v___x_2277_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_fst_2270_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2282_ = lean_box(v_res_2262_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v___x_2281_);
lean_ctor_set(v___x_2272_, 0, v___x_2282_);
v___x_2284_ = v___x_2272_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2281_);
v___x_2284_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2286_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v___x_2284_);
v___x_2286_ = v___x_2268_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_pos_2266_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2295_; lean_object* v_err_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
v_pos_2295_ = lean_ctor_get(v___x_2263_, 0);
v_err_2296_ = lean_ctor_get(v___x_2263_, 1);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2263_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_err_2296_);
lean_inc(v_pos_2295_);
lean_dec(v___x_2263_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_pos_2295_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_err_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_2361_, v_a_2362_);
lean_dec_ref(v_limits_2361_);
return v_res_2363_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_2364_){
_start:
{
uint32_t v___x_2365_; uint32_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2365_ = lean_uint8_to_uint32(v___y_2364_);
v___x_2366_ = 32;
v___x_2367_ = lean_uint32_dec_eq(v___x_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
uint32_t v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = 9;
v___x_2369_ = lean_uint32_dec_eq(v___x_2365_, v___x_2368_);
return v___x_2369_;
}
else
{
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_2370_){
_start:
{
uint8_t v___y_3754__boxed_2371_; uint8_t v_res_2372_; lean_object* v_r_2373_; 
v___y_3754__boxed_2371_ = lean_unbox(v___y_2370_);
v_res_2372_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_3754__boxed_2371_);
v_r_2373_ = lean_box(v_res_2372_);
return v_r_2373_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(uint8_t v___y_2374_){
_start:
{
uint32_t v___x_2375_; uint8_t v___y_2377_; uint32_t v___x_2382_; uint8_t v___x_2383_; 
v___x_2375_ = lean_uint8_to_uint32(v___y_2374_);
v___x_2382_ = 33;
v___x_2383_ = lean_uint32_dec_le(v___x_2382_, v___x_2375_);
if (v___x_2383_ == 0)
{
v___y_2377_ = v___x_2383_;
goto v___jp_2376_;
}
else
{
uint32_t v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = 126;
v___x_2385_ = lean_uint32_dec_le(v___x_2375_, v___x_2384_);
v___y_2377_ = v___x_2385_;
goto v___jp_2376_;
}
v___jp_2376_:
{
if (v___y_2377_ == 0)
{
uint32_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = 32;
v___x_2379_ = lean_uint32_dec_eq(v___x_2375_, v___x_2378_);
if (v___x_2379_ == 0)
{
uint32_t v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = 9;
v___x_2381_ = lean_uint32_dec_eq(v___x_2375_, v___x_2380_);
return v___x_2381_;
}
else
{
return v___x_2379_;
}
}
else
{
return v___y_2377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed(lean_object* v___y_2386_){
_start:
{
uint8_t v___y_3767__boxed_2387_; uint8_t v_res_2388_; lean_object* v_r_2389_; 
v___y_3767__boxed_2387_ = lean_unbox(v___y_2386_);
v_res_2388_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(v___y_3767__boxed_2387_);
v_r_2389_ = lean_box(v_res_2388_);
return v_r_2389_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_2390_, lean_object* v_pos_2391_){
_start:
{
lean_object* v_str_2392_; lean_object* v_startInclusive_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v_decide_2397_; 
v_str_2392_ = lean_ctor_get(v_s_2390_, 0);
v_startInclusive_2393_ = lean_ctor_get(v_s_2390_, 1);
v___x_2394_ = lean_nat_add(v_startInclusive_2393_, v_pos_2391_);
v___x_2395_ = lean_nat_sub(v___x_2394_, v_startInclusive_2393_);
v___x_2396_ = lean_unsigned_to_nat(0u);
v_decide_2397_ = lean_nat_dec_eq(v___x_2395_, v___x_2396_);
if (v_decide_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2406_; uint32_t v___x_2407_; uint32_t v___x_2408_; uint8_t v___x_2409_; 
lean_inc(v_startInclusive_2393_);
lean_inc_ref(v_str_2392_);
v___x_2398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2398_, 0, v_str_2392_);
lean_ctor_set(v___x_2398_, 1, v_startInclusive_2393_);
lean_ctor_set(v___x_2398_, 2, v___x_2394_);
v___x_2399_ = lean_unsigned_to_nat(1u);
v___x_2400_ = lean_nat_sub(v___x_2395_, v___x_2399_);
lean_dec(v___x_2395_);
v___x_2401_ = l_String_Slice_posLE(v___x_2398_, v___x_2400_);
lean_dec_ref_known(v___x_2398_, 3);
v___x_2406_ = lean_nat_add(v_startInclusive_2393_, v___x_2401_);
v___x_2407_ = lean_string_utf8_get_fast(v_str_2392_, v___x_2406_);
lean_dec(v___x_2406_);
v___x_2408_ = 32;
v___x_2409_ = lean_uint32_dec_eq(v___x_2407_, v___x_2408_);
if (v___x_2409_ == 0)
{
uint32_t v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = 9;
v___x_2411_ = lean_uint32_dec_eq(v___x_2407_, v___x_2410_);
if (v___x_2411_ == 0)
{
uint32_t v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = 13;
v___x_2413_ = lean_uint32_dec_eq(v___x_2407_, v___x_2412_);
if (v___x_2413_ == 0)
{
uint32_t v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = 10;
v___x_2415_ = lean_uint32_dec_eq(v___x_2407_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_dec(v___x_2401_);
return v_pos_2391_;
}
else
{
goto v___jp_2402_;
}
}
else
{
goto v___jp_2402_;
}
}
else
{
goto v___jp_2402_;
}
}
else
{
goto v___jp_2402_;
}
v___jp_2402_:
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = lean_nat_add(v___x_2401_, v___x_2399_);
v___x_2404_ = lean_nat_dec_le(v___x_2403_, v_pos_2391_);
lean_dec(v___x_2403_);
if (v___x_2404_ == 0)
{
lean_dec(v___x_2401_);
return v_pos_2391_;
}
else
{
lean_dec(v_pos_2391_);
v_pos_2391_ = v___x_2401_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2395_);
lean_dec(v___x_2394_);
return v_pos_2391_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_2416_, lean_object* v_pos_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_2416_, v_pos_2417_);
lean_dec_ref(v_s_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_pos_2427_; lean_object* v_pos_2431_; lean_object* v_maxHeaderNameLength_2434_; lean_object* v_maxHeaderValueLength_2435_; lean_object* v_maxSpaceSequence_2436_; lean_object* v___f_2437_; lean_object* v___x_2438_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2498_; lean_object* v_pos_2499_; lean_object* v_res_2500_; lean_object* v___x_2506_; lean_object* v_snd_2507_; lean_object* v_snd_2508_; uint8_t v___x_2509_; 
v_maxHeaderNameLength_2434_ = lean_ctor_get(v_limits_2424_, 6);
v_maxHeaderValueLength_2435_ = lean_ctor_get(v_limits_2424_, 7);
v_maxSpaceSequence_2436_ = lean_ctor_get(v_limits_2424_, 8);
v___f_2437_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2438_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2425_);
v___x_2506_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2437_, v_maxHeaderNameLength_2434_, v___x_2438_, v_a_2425_);
v_snd_2507_ = lean_ctor_get(v___x_2506_, 1);
lean_inc(v_snd_2507_);
v_snd_2508_ = lean_ctor_get(v_snd_2507_, 1);
v___x_2509_ = lean_unbox(v_snd_2508_);
if (v___x_2509_ == 0)
{
lean_object* v_fst_2510_; lean_object* v_fst_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2669_; 
v_fst_2510_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_fst_2510_);
lean_dec_ref(v___x_2506_);
v_fst_2511_ = lean_ctor_get(v_snd_2507_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_snd_2507_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; 
v_unused_2670_ = lean_ctor_get(v_snd_2507_, 1);
lean_dec(v_unused_2670_);
v___x_2513_ = v_snd_2507_;
v_isShared_2514_ = v_isSharedCheck_2669_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_fst_2511_);
lean_dec(v_snd_2507_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2669_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
uint8_t v___x_2515_; 
v___x_2515_ = lean_nat_dec_eq(v_fst_2510_, v___x_2438_);
if (v___x_2515_ == 0)
{
lean_object* v_array_2516_; lean_object* v_idx_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2664_; 
v_array_2516_ = lean_ctor_get(v_a_2425_, 0);
v_idx_2517_ = lean_ctor_get(v_a_2425_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_a_2425_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2519_ = v_a_2425_;
v_isShared_2520_ = v_isSharedCheck_2664_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_idx_2517_);
lean_inc(v_array_2516_);
lean_dec(v_a_2425_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2664_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___f_2521_; lean_object* v___y_2523_; lean_object* v_pos_2524_; lean_object* v_res_2525_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v_lower_2555_; lean_object* v_upper_2556_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___f_2567_; lean_object* v___y_2569_; lean_object* v_pos_2570_; lean_object* v___y_2597_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___y_2655_; uint8_t v___x_2663_; 
v___f_2521_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___f_2567_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_2652_ = lean_nat_add(v_idx_2517_, v_fst_2510_);
lean_dec(v_fst_2510_);
v___x_2653_ = lean_byte_array_size(v_array_2516_);
v___x_2663_ = lean_nat_dec_le(v_idx_2517_, v___x_2438_);
if (v___x_2663_ == 0)
{
v___y_2655_ = v_idx_2517_;
goto v___jp_2654_;
}
else
{
lean_dec(v_idx_2517_);
v___y_2655_ = v___x_2438_;
goto v___jp_2654_;
}
v___jp_2522_:
{
lean_object* v___x_2526_; lean_object* v_snd_2527_; lean_object* v_snd_2528_; uint8_t v___x_2529_; 
v___x_2526_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2521_, v_maxSpaceSequence_2436_, v___x_2438_, v_pos_2524_);
v_snd_2527_ = lean_ctor_get(v___x_2526_, 1);
lean_inc(v_snd_2527_);
lean_dec_ref(v___x_2526_);
v_snd_2528_ = lean_ctor_get(v_snd_2527_, 1);
v___x_2529_ = lean_unbox(v_snd_2528_);
if (v___x_2529_ == 0)
{
lean_object* v_fst_2530_; lean_object* v_array_2531_; lean_object* v_idx_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_fst_2530_ = lean_ctor_get(v_snd_2527_, 0);
lean_inc(v_fst_2530_);
lean_dec(v_snd_2527_);
v_array_2531_ = lean_ctor_get(v_fst_2530_, 0);
v_idx_2532_ = lean_ctor_get(v_fst_2530_, 1);
v___x_2533_ = lean_byte_array_size(v_array_2531_);
v___x_2534_ = lean_nat_dec_lt(v_idx_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
v___y_2498_ = v___y_2523_;
v_pos_2499_ = v_fst_2530_;
v_res_2500_ = v_res_2525_;
goto v___jp_2497_;
}
else
{
uint8_t v___x_2535_; uint32_t v___x_2536_; uint32_t v___x_2537_; uint8_t v___x_2538_; 
v___x_2535_ = lean_byte_array_fget(v_array_2531_, v_idx_2532_);
v___x_2536_ = lean_uint8_to_uint32(v___x_2535_);
v___x_2537_ = 32;
v___x_2538_ = lean_uint32_dec_eq(v___x_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
uint32_t v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = 9;
v___x_2540_ = lean_uint32_dec_eq(v___x_2536_, v___x_2539_);
if (v___x_2540_ == 0)
{
v___y_2498_ = v___y_2523_;
v_pos_2499_ = v_fst_2530_;
v_res_2500_ = v_res_2525_;
goto v___jp_2497_;
}
else
{
lean_dec(v_res_2525_);
lean_dec_ref(v___y_2523_);
v_pos_2431_ = v_fst_2530_;
goto v___jp_2430_;
}
}
else
{
lean_dec(v_res_2525_);
lean_dec_ref(v___y_2523_);
v_pos_2431_ = v_fst_2530_;
goto v___jp_2430_;
}
}
}
else
{
lean_object* v_fst_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_res_2525_);
lean_dec_ref(v___y_2523_);
v_fst_2541_ = lean_ctor_get(v_snd_2527_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_snd_2527_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v_snd_2527_, 1);
lean_dec(v_unused_2550_);
v___x_2543_ = v_snd_2527_;
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_fst_2541_);
lean_dec(v_snd_2527_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_box(0);
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 1);
lean_ctor_set(v___x_2543_, 1, v___x_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_fst_2541_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
v___jp_2551_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = l_ByteArray_toByteSlice(v___y_2554_, v_lower_2555_, v_upper_2556_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
v___y_2523_ = v___y_2552_;
v_pos_2524_ = v___y_2553_;
v_res_2525_ = v___x_2558_;
goto v___jp_2522_;
}
v___jp_2559_:
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_nat_dec_le(v___y_2562_, v___y_2563_);
if (v___x_2566_ == 0)
{
lean_dec(v___y_2562_);
v___y_2552_ = v___y_2561_;
v___y_2553_ = v___y_2560_;
v___y_2554_ = v___y_2564_;
v_lower_2555_ = v___y_2565_;
v_upper_2556_ = v___y_2563_;
goto v___jp_2551_;
}
else
{
lean_dec(v___y_2563_);
v___y_2552_ = v___y_2561_;
v___y_2553_ = v___y_2560_;
v___y_2554_ = v___y_2564_;
v_lower_2555_ = v___y_2565_;
v_upper_2556_ = v___y_2562_;
goto v___jp_2551_;
}
}
v___jp_2568_:
{
lean_object* v___x_2571_; lean_object* v_snd_2572_; lean_object* v_snd_2573_; uint8_t v___x_2574_; 
lean_inc_ref(v_pos_2570_);
v___x_2571_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2567_, v_maxHeaderValueLength_2435_, v___x_2438_, v_pos_2570_);
v_snd_2572_ = lean_ctor_get(v___x_2571_, 1);
lean_inc(v_snd_2572_);
v_snd_2573_ = lean_ctor_get(v_snd_2572_, 1);
v___x_2574_ = lean_unbox(v_snd_2573_);
if (v___x_2574_ == 0)
{
lean_object* v_fst_2575_; lean_object* v_fst_2576_; lean_object* v_array_2577_; lean_object* v_idx_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v_fst_2575_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_fst_2575_);
lean_dec_ref(v___x_2571_);
v_fst_2576_ = lean_ctor_get(v_snd_2572_, 0);
lean_inc(v_fst_2576_);
lean_dec(v_snd_2572_);
v_array_2577_ = lean_ctor_get(v_pos_2570_, 0);
lean_inc_ref(v_array_2577_);
v_idx_2578_ = lean_ctor_get(v_pos_2570_, 1);
lean_inc(v_idx_2578_);
lean_dec_ref(v_pos_2570_);
v___x_2579_ = lean_nat_add(v_idx_2578_, v_fst_2575_);
lean_dec(v_fst_2575_);
v___x_2580_ = lean_byte_array_size(v_array_2577_);
v___x_2581_ = lean_nat_dec_le(v_idx_2578_, v___x_2438_);
if (v___x_2581_ == 0)
{
v___y_2560_ = v_fst_2576_;
v___y_2561_ = v___y_2569_;
v___y_2562_ = v___x_2579_;
v___y_2563_ = v___x_2580_;
v___y_2564_ = v_array_2577_;
v___y_2565_ = v_idx_2578_;
goto v___jp_2559_;
}
else
{
lean_dec(v_idx_2578_);
v___y_2560_ = v_fst_2576_;
v___y_2561_ = v___y_2569_;
v___y_2562_ = v___x_2579_;
v___y_2563_ = v___x_2580_;
v___y_2564_ = v_array_2577_;
v___y_2565_ = v___x_2438_;
goto v___jp_2559_;
}
}
else
{
lean_object* v_fst_2582_; lean_object* v_idx_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2594_; 
lean_dec_ref(v___x_2571_);
v_fst_2582_ = lean_ctor_get(v_snd_2572_, 0);
lean_inc(v_fst_2582_);
lean_dec(v_snd_2572_);
v_idx_2583_ = lean_ctor_get(v_pos_2570_, 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_pos_2570_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v_pos_2570_, 0);
lean_dec(v_unused_2595_);
v___x_2585_ = v_pos_2570_;
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_idx_2583_);
lean_dec(v_pos_2570_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v_idx_2587_; uint8_t v___x_2588_; 
v_idx_2587_ = lean_ctor_get(v_fst_2582_, 1);
v___x_2588_ = lean_nat_dec_eq(v_idx_2583_, v_idx_2587_);
lean_dec(v_idx_2583_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_dec_ref(v___y_2569_);
v___x_2589_ = lean_box(0);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 1, v___x_2589_);
lean_ctor_set(v___x_2585_, 0, v_fst_2582_);
v___x_2591_ = v___x_2585_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_fst_2582_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
else
{
lean_object* v___x_2593_; 
lean_del_object(v___x_2585_);
v___x_2593_ = lean_box(0);
v___y_2523_ = v___y_2569_;
v_pos_2524_ = v_fst_2582_;
v_res_2525_ = v___x_2593_;
goto v___jp_2522_;
}
}
}
}
v___jp_2596_:
{
lean_object* v_array_2598_; lean_object* v_idx_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_array_2598_ = lean_ctor_get(v_fst_2511_, 0);
v_idx_2599_ = lean_ctor_get(v_fst_2511_, 1);
v___x_2600_ = lean_byte_array_size(v_array_2598_);
v___x_2601_ = lean_nat_dec_lt(v_idx_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_array_2516_);
v___x_2602_ = lean_box(0);
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 1);
lean_ctor_set(v___x_2519_, 1, v___x_2602_);
lean_ctor_set(v___x_2519_, 0, v_fst_2511_);
v___x_2604_ = v___x_2519_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_fst_2511_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
else
{
uint8_t v___x_2606_; uint8_t v_got_2607_; uint8_t v___x_2608_; 
v___x_2606_ = 58;
v_got_2607_ = lean_byte_array_fget(v_array_2598_, v_idx_2599_);
v___x_2608_ = lean_uint8_dec_eq(v_got_2607_, v___x_2606_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_array_2516_);
v___x_2609_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 1);
lean_ctor_set(v___x_2519_, 1, v___x_2609_);
lean_ctor_set(v___x_2519_, 0, v_fst_2511_);
v___x_2611_ = v___x_2519_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_fst_2511_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
else
{
lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2649_; 
lean_inc(v_idx_2599_);
lean_inc_ref(v_array_2598_);
lean_del_object(v___x_2519_);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_fst_2511_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; lean_object* v_unused_2651_; 
v_unused_2650_ = lean_ctor_get(v_fst_2511_, 1);
lean_dec(v_unused_2650_);
v_unused_2651_ = lean_ctor_get(v_fst_2511_, 0);
lean_dec(v_unused_2651_);
v___x_2614_ = v_fst_2511_;
v_isShared_2615_ = v_isSharedCheck_2649_;
goto v_resetjp_2613_;
}
else
{
lean_dec(v_fst_2511_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2649_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_nat_add(v_idx_2599_, v___x_2616_);
lean_dec(v_idx_2599_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 1, v___x_2617_);
v___x_2619_ = v___x_2614_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_array_2598_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2620_; lean_object* v_snd_2621_; lean_object* v_snd_2622_; uint8_t v___x_2623_; 
v___x_2620_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2521_, v_maxSpaceSequence_2436_, v___x_2438_, v___x_2619_);
v_snd_2621_ = lean_ctor_get(v___x_2620_, 1);
lean_inc(v_snd_2621_);
lean_dec_ref(v___x_2620_);
v_snd_2622_ = lean_ctor_get(v_snd_2621_, 1);
v___x_2623_ = lean_unbox(v_snd_2622_);
if (v___x_2623_ == 0)
{
lean_object* v_fst_2624_; lean_object* v_array_2625_; lean_object* v_idx_2626_; lean_object* v_lower_2627_; lean_object* v_upper_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v_fst_2624_ = lean_ctor_get(v_snd_2621_, 0);
lean_inc(v_fst_2624_);
lean_dec(v_snd_2621_);
v_array_2625_ = lean_ctor_get(v_fst_2624_, 0);
v_idx_2626_ = lean_ctor_get(v_fst_2624_, 1);
v_lower_2627_ = lean_ctor_get(v___y_2597_, 0);
lean_inc(v_lower_2627_);
v_upper_2628_ = lean_ctor_get(v___y_2597_, 1);
lean_inc(v_upper_2628_);
lean_dec_ref(v___y_2597_);
v___x_2629_ = l_ByteArray_toByteSlice(v_array_2516_, v_lower_2627_, v_upper_2628_);
v___x_2630_ = lean_byte_array_size(v_array_2625_);
v___x_2631_ = lean_nat_dec_lt(v_idx_2626_, v___x_2630_);
if (v___x_2631_ == 0)
{
v___y_2569_ = v___x_2629_;
v_pos_2570_ = v_fst_2624_;
goto v___jp_2568_;
}
else
{
uint8_t v___x_2632_; uint32_t v___x_2633_; uint32_t v___x_2634_; uint8_t v___x_2635_; 
v___x_2632_ = lean_byte_array_fget(v_array_2625_, v_idx_2626_);
v___x_2633_ = lean_uint8_to_uint32(v___x_2632_);
v___x_2634_ = 32;
v___x_2635_ = lean_uint32_dec_eq(v___x_2633_, v___x_2634_);
if (v___x_2635_ == 0)
{
uint32_t v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = 9;
v___x_2637_ = lean_uint32_dec_eq(v___x_2633_, v___x_2636_);
if (v___x_2637_ == 0)
{
v___y_2569_ = v___x_2629_;
v_pos_2570_ = v_fst_2624_;
goto v___jp_2568_;
}
else
{
lean_dec_ref(v___x_2629_);
v_pos_2427_ = v_fst_2624_;
goto v___jp_2426_;
}
}
else
{
lean_dec_ref(v___x_2629_);
v_pos_2427_ = v_fst_2624_;
goto v___jp_2426_;
}
}
}
else
{
lean_object* v_fst_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_array_2516_);
v_fst_2638_ = lean_ctor_get(v_snd_2621_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_snd_2621_);
if (v_isSharedCheck_2646_ == 0)
{
lean_object* v_unused_2647_; 
v_unused_2647_ = lean_ctor_get(v_snd_2621_, 1);
lean_dec(v_unused_2647_);
v___x_2640_ = v_snd_2621_;
v_isShared_2641_ = v_isSharedCheck_2646_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_fst_2638_);
lean_dec(v_snd_2621_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2646_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = lean_box(0);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 1);
lean_ctor_set(v___x_2640_, 1, v___x_2642_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_fst_2638_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
}
}
v___jp_2654_:
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_nat_dec_le(v___x_2652_, v___x_2653_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2658_; 
lean_dec(v___x_2652_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v___x_2653_);
lean_ctor_set(v___x_2513_, 0, v___y_2655_);
v___x_2658_ = v___x_2513_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___y_2655_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
v___y_2597_ = v___x_2658_;
goto v___jp_2596_;
}
}
else
{
lean_object* v___x_2661_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v___x_2652_);
lean_ctor_set(v___x_2513_, 0, v___y_2655_);
v___x_2661_ = v___x_2513_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___y_2655_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2652_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
v___y_2597_ = v___x_2661_;
goto v___jp_2596_;
}
}
}
}
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
lean_dec(v_fst_2511_);
lean_dec(v_fst_2510_);
v___x_2665_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2514_ == 0)
{
lean_ctor_set_tag(v___x_2513_, 1);
lean_ctor_set(v___x_2513_, 1, v___x_2665_);
lean_ctor_set(v___x_2513_, 0, v_a_2425_);
v___x_2667_ = v___x_2513_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2425_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_object* v_fst_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref(v___x_2506_);
lean_dec_ref(v_a_2425_);
v_fst_2671_ = lean_ctor_get(v_snd_2507_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_snd_2507_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v_snd_2507_, 1);
lean_dec(v_unused_2680_);
v___x_2673_ = v_snd_2507_;
v_isShared_2674_ = v_isSharedCheck_2679_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_fst_2671_);
lean_dec(v_snd_2507_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2679_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2675_ = lean_box(0);
if (v_isShared_2674_ == 0)
{
lean_ctor_set_tag(v___x_2673_, 1);
lean_ctor_set(v___x_2673_, 1, v___x_2675_);
v___x_2677_ = v___x_2673_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_fst_2671_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
v___jp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_pos_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
return v___x_2429_;
}
v___jp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_pos_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
return v___x_2433_;
}
v___jp_2439_:
{
lean_object* v___x_2443_; 
v___x_2443_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2442_, v___y_2441_);
lean_dec(v___y_2442_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_pos_2444_; lean_object* v_res_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2458_; 
v_pos_2444_ = lean_ctor_get(v___x_2443_, 0);
v_res_2445_ = lean_ctor_get(v___x_2443_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2447_ = v___x_2443_;
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_res_2445_);
lean_inc(v_pos_2444_);
lean_dec(v___x_2443_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2449_ = lean_string_utf8_byte_size(v_res_2445_);
lean_inc(v_res_2445_);
v___x_2450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2450_, 0, v_res_2445_);
lean_ctor_set(v___x_2450_, 1, v___x_2438_);
lean_ctor_set(v___x_2450_, 2, v___x_2449_);
v___x_2451_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_2450_, v___x_2449_);
lean_dec_ref_known(v___x_2450_, 3);
v___x_2452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2452_, 0, v_res_2445_);
lean_ctor_set(v___x_2452_, 1, v___x_2438_);
lean_ctor_set(v___x_2452_, 2, v___x_2451_);
v___x_2453_ = l_String_Slice_toString(v___x_2452_);
lean_dec_ref_known(v___x_2452_, 3);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___y_2440_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v___x_2454_);
v___x_2456_ = v___x_2447_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_pos_2444_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_pos_2459_; lean_object* v_err_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v___y_2440_);
v_pos_2459_ = lean_ctor_get(v___x_2443_, 0);
v_err_2460_ = lean_ctor_get(v___x_2443_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2443_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_err_2460_);
lean_inc(v_pos_2459_);
lean_dec(v___x_2443_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_pos_2459_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_err_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
v___jp_2468_:
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_string_validate_utf8(v___y_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
lean_dec_ref(v___y_2471_);
v___x_2473_ = lean_box(0);
v___y_2440_ = v___y_2469_;
v___y_2441_ = v___y_2470_;
v___y_2442_ = v___x_2473_;
goto v___jp_2439_;
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_string_from_utf8_unchecked(v___y_2471_);
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
v___y_2440_ = v___y_2469_;
v___y_2441_ = v___y_2470_;
v___y_2442_ = v___x_2475_;
goto v___jp_2439_;
}
}
v___jp_2476_:
{
lean_object* v___x_2480_; 
v___x_2480_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2479_, v___y_2477_);
lean_dec(v___y_2479_);
if (lean_obj_tag(v___x_2480_) == 0)
{
if (lean_obj_tag(v___y_2478_) == 0)
{
lean_object* v_pos_2481_; lean_object* v_res_2482_; lean_object* v___x_2483_; 
v_pos_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_pos_2481_);
v_res_2482_ = lean_ctor_get(v___x_2480_, 1);
lean_inc(v_res_2482_);
lean_dec_ref_known(v___x_2480_, 2);
v___x_2483_ = l_ByteArray_empty;
v___y_2469_ = v_res_2482_;
v___y_2470_ = v_pos_2481_;
v___y_2471_ = v___x_2483_;
goto v___jp_2468_;
}
else
{
lean_object* v_pos_2484_; lean_object* v_res_2485_; lean_object* v_val_2486_; lean_object* v___x_2487_; 
v_pos_2484_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_pos_2484_);
v_res_2485_ = lean_ctor_get(v___x_2480_, 1);
lean_inc(v_res_2485_);
lean_dec_ref_known(v___x_2480_, 2);
v_val_2486_ = lean_ctor_get(v___y_2478_, 0);
lean_inc(v_val_2486_);
lean_dec_ref_known(v___y_2478_, 1);
v___x_2487_ = l_ByteSlice_toByteArray(v_val_2486_);
v___y_2469_ = v_res_2485_;
v___y_2470_ = v_pos_2484_;
v___y_2471_ = v___x_2487_;
goto v___jp_2468_;
}
}
else
{
lean_object* v_pos_2488_; lean_object* v_err_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v___y_2478_);
v_pos_2488_ = lean_ctor_get(v___x_2480_, 0);
v_err_2489_ = lean_ctor_get(v___x_2480_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2480_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_err_2489_);
lean_inc(v_pos_2488_);
lean_dec(v___x_2480_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_pos_2488_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_err_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
v___jp_2497_:
{
lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2501_ = l_ByteSlice_toByteArray(v___y_2498_);
v___x_2502_ = lean_string_validate_utf8(v___x_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
lean_dec_ref(v___x_2501_);
v___x_2503_ = lean_box(0);
v___y_2477_ = v_pos_2499_;
v___y_2478_ = v_res_2500_;
v___y_2479_ = v___x_2503_;
goto v___jp_2476_;
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_string_from_utf8_unchecked(v___x_2501_);
v___x_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
v___y_2477_ = v_pos_2499_;
v___y_2478_ = v_res_2500_;
v___y_2479_ = v___x_2505_;
goto v___jp_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2681_, v_a_2682_);
lean_dec_ref(v_limits_2681_);
return v_res_2683_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2684_, lean_object* v_x_2685_){
_start:
{
if (lean_obj_tag(v_x_2684_) == 0)
{
if (lean_obj_tag(v_x_2685_) == 0)
{
uint8_t v___x_2686_; 
v___x_2686_ = 1;
return v___x_2686_;
}
else
{
uint8_t v___x_2687_; 
v___x_2687_ = 0;
return v___x_2687_;
}
}
else
{
if (lean_obj_tag(v_x_2685_) == 0)
{
uint8_t v___x_2688_; 
v___x_2688_ = 0;
return v___x_2688_;
}
else
{
lean_object* v_val_2689_; lean_object* v_val_2690_; uint8_t v___x_2691_; uint8_t v___x_2692_; uint8_t v___x_2693_; 
v_val_2689_ = lean_ctor_get(v_x_2684_, 0);
v_val_2690_ = lean_ctor_get(v_x_2685_, 0);
v___x_2691_ = lean_unbox(v_val_2689_);
v___x_2692_ = lean_unbox(v_val_2690_);
v___x_2693_ = lean_uint8_dec_eq(v___x_2691_, v___x_2692_);
return v___x_2693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2694_, lean_object* v_x_2695_){
_start:
{
uint8_t v_res_2696_; lean_object* v_r_2697_; 
v_res_2696_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2694_, v_x_2695_);
lean_dec(v_x_2695_);
lean_dec(v_x_2694_);
v_r_2697_ = lean_box(v_res_2696_);
return v_r_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_pos_2707_; lean_object* v_res_2708_; lean_object* v___y_2712_; uint8_t v___y_2713_; lean_object* v_pos_2762_; lean_object* v_res_2763_; lean_object* v_array_2768_; lean_object* v_idx_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_array_2768_ = lean_ctor_get(v_a_2705_, 0);
v_idx_2769_ = lean_ctor_get(v_a_2705_, 1);
v___x_2770_ = lean_byte_array_size(v_array_2768_);
v___x_2771_ = lean_nat_dec_lt(v_idx_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_box(0);
v_pos_2762_ = v_a_2705_;
v_res_2763_ = v___x_2772_;
goto v___jp_2761_;
}
else
{
uint8_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = lean_byte_array_fget(v_array_2768_, v_idx_2769_);
v___x_2774_ = lean_box(v___x_2773_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
v_pos_2762_ = v_a_2705_;
v_res_2763_ = v___x_2775_;
goto v___jp_2761_;
}
v___jp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_res_2708_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_pos_2707_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
return v___x_2710_;
}
v___jp_2711_:
{
if (v___y_2713_ == 0)
{
lean_object* v___x_2714_; 
v___x_2714_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2704_, v___y_2712_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_pos_2715_; lean_object* v_res_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_pos_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_pos_2715_);
v_res_2716_ = lean_ctor_get(v___x_2714_, 1);
lean_inc(v_res_2716_);
lean_dec_ref_known(v___x_2714_, 2);
v___x_2717_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2718_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2717_, v_pos_2715_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_pos_2719_; 
v_pos_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_pos_2719_);
lean_dec_ref_known(v___x_2718_, 2);
v_pos_2707_ = v_pos_2719_;
v_res_2708_ = v_res_2716_;
goto v___jp_2706_;
}
else
{
lean_object* v_pos_2720_; lean_object* v_err_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_res_2716_);
v_pos_2720_ = lean_ctor_get(v___x_2718_, 0);
v_err_2721_ = lean_ctor_get(v___x_2718_, 1);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2718_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_err_2721_);
lean_inc(v_pos_2720_);
lean_dec(v___x_2718_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_pos_2720_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_err_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_pos_2729_; lean_object* v_res_2730_; 
v_pos_2729_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_pos_2729_);
v_res_2730_ = lean_ctor_get(v___x_2714_, 1);
lean_inc(v_res_2730_);
lean_dec_ref_known(v___x_2714_, 2);
v_pos_2707_ = v_pos_2729_;
v_res_2708_ = v_res_2730_;
goto v___jp_2706_;
}
else
{
lean_object* v_pos_2731_; lean_object* v_err_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
v_pos_2731_ = lean_ctor_get(v___x_2714_, 0);
v_err_2732_ = lean_ctor_get(v___x_2714_, 1);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2714_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_err_2732_);
lean_inc(v_pos_2731_);
lean_dec(v___x_2714_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_pos_2731_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_err_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2741_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2740_, v___y_2712_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_pos_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2750_; 
v_pos_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v___x_2741_, 1);
lean_dec(v_unused_2751_);
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2750_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_pos_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2750_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2746_ = lean_box(0);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 1, v___x_2746_);
v___x_2748_ = v___x_2744_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_pos_2742_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
else
{
lean_object* v_pos_2752_; lean_object* v_err_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_pos_2752_ = lean_ctor_get(v___x_2741_, 0);
v_err_2753_ = lean_ctor_get(v___x_2741_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2741_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_err_2753_);
lean_inc(v_pos_2752_);
lean_dec(v___x_2741_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_pos_2752_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_err_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
v___jp_2761_:
{
lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_2765_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2763_, v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2766_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_2767_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2763_, v___x_2766_);
lean_dec(v_res_2763_);
v___y_2712_ = v_pos_2762_;
v___y_2713_ = v___x_2767_;
goto v___jp_2711_;
}
else
{
lean_dec(v_res_2763_);
v___y_2712_ = v_pos_2762_;
v___y_2713_ = v___x_2765_;
goto v___jp_2711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2776_, v_a_2777_);
lean_dec_ref(v_limits_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2783_){
_start:
{
lean_object* v_array_2784_; lean_object* v_idx_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v_array_2784_ = lean_ctor_get(v_a_2783_, 0);
v_idx_2785_ = lean_ctor_get(v_a_2783_, 1);
v___x_2786_ = lean_byte_array_size(v_array_2784_);
v___x_2787_ = lean_nat_dec_lt(v_idx_2785_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_box(0);
v___x_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2789_, 0, v_a_2783_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
return v___x_2789_;
}
else
{
uint8_t v___x_2790_; uint8_t v_got_2791_; uint8_t v___x_2792_; 
v___x_2790_ = 92;
v_got_2791_ = lean_byte_array_fget(v_array_2784_, v_idx_2785_);
v___x_2792_ = lean_uint8_dec_eq(v_got_2791_, v___x_2790_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_2794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_a_2783_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
return v___x_2794_;
}
else
{
lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2829_; 
lean_inc(v_idx_2785_);
lean_inc_ref(v_array_2784_);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_a_2783_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; lean_object* v_unused_2831_; 
v_unused_2830_ = lean_ctor_get(v_a_2783_, 1);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_a_2783_, 0);
lean_dec(v_unused_2831_);
v___x_2796_ = v_a_2783_;
v_isShared_2797_ = v_isSharedCheck_2829_;
goto v_resetjp_2795_;
}
else
{
lean_dec(v_a_2783_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2829_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2798_ = lean_unsigned_to_nat(1u);
v___x_2799_ = lean_nat_add(v_idx_2785_, v___x_2798_);
lean_dec(v_idx_2785_);
v___x_2800_ = lean_nat_dec_lt(v___x_2799_, v___x_2786_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2802_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2799_);
v___x_2802_ = v___x_2796_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_array_2784_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___x_2799_);
v___x_2802_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
return v___x_2804_;
}
}
else
{
uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2806_ = lean_byte_array_fget(v_array_2784_, v___x_2799_);
v___x_2807_ = lean_nat_add(v___x_2799_, v___x_2798_);
lean_dec(v___x_2799_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2807_);
v___x_2809_ = v___x_2796_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_array_2784_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint32_t v___x_2812_; uint8_t v___y_2814_; uint32_t v___x_2820_; uint8_t v___x_2821_; 
v___x_2810_ = lean_box(v___x_2806_);
lean_inc_ref(v___x_2809_);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_uint8_to_uint32(v___x_2806_);
v___x_2820_ = 9;
v___x_2821_ = lean_uint32_dec_eq(v___x_2812_, v___x_2820_);
if (v___x_2821_ == 0)
{
uint32_t v___x_2822_; uint8_t v___x_2823_; 
v___x_2822_ = 32;
v___x_2823_ = lean_uint32_dec_eq(v___x_2812_, v___x_2822_);
if (v___x_2823_ == 0)
{
uint32_t v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = 33;
v___x_2825_ = lean_uint32_dec_le(v___x_2824_, v___x_2812_);
if (v___x_2825_ == 0)
{
v___y_2814_ = v___x_2825_;
goto v___jp_2813_;
}
else
{
uint32_t v___x_2826_; uint8_t v___x_2827_; 
v___x_2826_ = 126;
v___x_2827_ = lean_uint32_dec_le(v___x_2812_, v___x_2826_);
v___y_2814_ = v___x_2827_;
goto v___jp_2813_;
}
}
else
{
lean_dec_ref(v___x_2809_);
return v___x_2811_;
}
}
else
{
lean_dec_ref(v___x_2809_);
return v___x_2811_;
}
v___jp_2813_:
{
if (v___y_2814_ == 0)
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec_ref_known(v___x_2811_, 2);
v___x_2815_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2816_ = l_Char_quote(v___x_2812_);
v___x_2817_ = lean_string_append(v___x_2815_, v___x_2816_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2809_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
return v___x_2819_;
}
else
{
lean_dec_ref(v___x_2809_);
return v___x_2811_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2836_, lean_object* v_buf_2837_, lean_object* v_length_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_array_2840_; lean_object* v_idx_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v_array_2840_ = lean_ctor_get(v_a_2839_, 0);
v_idx_2841_ = lean_ctor_get(v_a_2839_, 1);
v___x_2842_ = lean_byte_array_size(v_array_2840_);
v___x_2843_ = lean_nat_dec_lt(v_idx_2841_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_dec(v_length_2838_);
lean_dec_ref(v_buf_2837_);
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_a_2839_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
return v___x_2845_;
}
else
{
lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2920_; 
lean_inc(v_idx_2841_);
lean_inc_ref(v_array_2840_);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_a_2839_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; lean_object* v_unused_2922_; 
v_unused_2921_ = lean_ctor_get(v_a_2839_, 1);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_a_2839_, 0);
lean_dec(v_unused_2922_);
v___x_2847_ = v_a_2839_;
v_isShared_2848_ = v_isSharedCheck_2920_;
goto v_resetjp_2846_;
}
else
{
lean_dec(v_a_2839_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2920_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
uint8_t v_c_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v_it_x27_2853_; 
v_c_2849_ = lean_byte_array_fget(v_array_2840_, v_idx_2841_);
v___x_2850_ = lean_unsigned_to_nat(1u);
v___x_2851_ = lean_nat_add(v_idx_2841_, v___x_2850_);
lean_dec(v_idx_2841_);
lean_inc(v___x_2851_);
lean_inc_ref(v_array_2840_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 1, v___x_2851_);
v_it_x27_2853_ = v___x_2847_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_array_2840_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2851_);
v_it_x27_2853_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
uint8_t v___x_2861_; uint8_t v___x_2862_; 
v___x_2861_ = 34;
v___x_2862_ = lean_uint8_dec_eq(v_c_2849_, v___x_2861_);
if (v___x_2862_ == 0)
{
uint8_t v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = 92;
v___x_2864_ = lean_uint8_dec_eq(v_c_2849_, v___x_2863_);
if (v___x_2864_ == 0)
{
uint32_t v___x_2865_; uint8_t v___y_2867_; uint8_t v___y_2874_; uint32_t v___x_2879_; uint8_t v___x_2880_; 
lean_dec(v___x_2851_);
lean_dec_ref(v_array_2840_);
v___x_2865_ = lean_uint8_to_uint32(v_c_2849_);
v___x_2879_ = 9;
v___x_2880_ = lean_uint32_dec_eq(v___x_2865_, v___x_2879_);
if (v___x_2880_ == 0)
{
uint32_t v___x_2881_; uint8_t v___x_2882_; 
v___x_2881_ = 32;
v___x_2882_ = lean_uint32_dec_eq(v___x_2865_, v___x_2881_);
if (v___x_2882_ == 0)
{
uint32_t v___x_2883_; uint8_t v___x_2884_; 
v___x_2883_ = 33;
v___x_2884_ = lean_uint32_dec_eq(v___x_2865_, v___x_2883_);
if (v___x_2884_ == 0)
{
uint32_t v___x_2885_; uint8_t v___x_2886_; 
v___x_2885_ = 35;
v___x_2886_ = lean_uint32_dec_le(v___x_2885_, v___x_2865_);
if (v___x_2886_ == 0)
{
v___y_2874_ = v___x_2886_;
goto v___jp_2873_;
}
else
{
uint32_t v___x_2887_; uint8_t v___x_2888_; 
v___x_2887_ = 91;
v___x_2888_ = lean_uint32_dec_le(v___x_2865_, v___x_2887_);
v___y_2874_ = v___x_2888_;
goto v___jp_2873_;
}
}
else
{
goto v___jp_2854_;
}
}
else
{
goto v___jp_2854_;
}
}
else
{
goto v___jp_2854_;
}
v___jp_2866_:
{
if (v___y_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec(v_length_2838_);
lean_dec_ref(v_buf_2837_);
v___x_2868_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2869_ = l_Char_quote(v___x_2865_);
v___x_2870_ = lean_string_append(v___x_2868_, v___x_2869_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2872_, 0, v_it_x27_2853_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
return v___x_2872_;
}
else
{
goto v___jp_2854_;
}
}
v___jp_2873_:
{
if (v___y_2874_ == 0)
{
uint32_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = 93;
v___x_2876_ = lean_uint32_dec_le(v___x_2875_, v___x_2865_);
if (v___x_2876_ == 0)
{
v___y_2867_ = v___x_2876_;
goto v___jp_2866_;
}
else
{
uint32_t v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = 126;
v___x_2878_ = lean_uint32_dec_le(v___x_2865_, v___x_2877_);
v___y_2867_ = v___x_2878_;
goto v___jp_2866_;
}
}
else
{
goto v___jp_2854_;
}
}
}
else
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_nat_dec_lt(v___x_2851_, v___x_2842_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v___x_2851_);
lean_dec_ref(v_array_2840_);
lean_dec(v_length_2838_);
lean_dec_ref(v_buf_2837_);
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2891_, 0, v_it_x27_2853_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
return v___x_2891_;
}
else
{
uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint32_t v___x_2902_; uint8_t v___y_2904_; uint32_t v___x_2910_; uint8_t v___x_2911_; 
lean_dec_ref(v_it_x27_2853_);
v___x_2892_ = lean_byte_array_fget(v_array_2840_, v___x_2851_);
v___x_2893_ = lean_nat_add(v___x_2851_, v___x_2850_);
lean_dec(v___x_2851_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_array_2840_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2902_ = lean_uint8_to_uint32(v___x_2892_);
v___x_2910_ = 9;
v___x_2911_ = lean_uint32_dec_eq(v___x_2902_, v___x_2910_);
if (v___x_2911_ == 0)
{
uint32_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = 32;
v___x_2913_ = lean_uint32_dec_eq(v___x_2902_, v___x_2912_);
if (v___x_2913_ == 0)
{
uint32_t v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = 33;
v___x_2915_ = lean_uint32_dec_le(v___x_2914_, v___x_2902_);
if (v___x_2915_ == 0)
{
v___y_2904_ = v___x_2915_;
goto v___jp_2903_;
}
else
{
uint32_t v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = 126;
v___x_2917_ = lean_uint32_dec_le(v___x_2902_, v___x_2916_);
v___y_2904_ = v___x_2917_;
goto v___jp_2903_;
}
}
else
{
goto v___jp_2895_;
}
}
else
{
goto v___jp_2895_;
}
v___jp_2895_:
{
lean_object* v___x_2896_; uint8_t v___x_2897_; 
v___x_2896_ = lean_nat_add(v_length_2838_, v___x_2850_);
lean_dec(v_length_2838_);
v___x_2897_ = lean_nat_dec_lt(v_maxLength_2836_, v___x_2896_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_byte_array_push(v_buf_2837_, v___x_2892_);
v_buf_2837_ = v___x_2898_;
v_length_2838_ = v___x_2896_;
v_a_2839_ = v___x_2894_;
goto _start;
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_dec(v___x_2896_);
lean_dec_ref(v_buf_2837_);
v___x_2900_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2894_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
return v___x_2901_;
}
}
v___jp_2903_:
{
if (v___y_2904_ == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec(v_length_2838_);
lean_dec_ref(v_buf_2837_);
v___x_2905_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2906_ = l_Char_quote(v___x_2902_);
v___x_2907_ = lean_string_append(v___x_2905_, v___x_2906_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2894_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
return v___x_2909_;
}
else
{
goto v___jp_2895_;
}
}
}
}
}
else
{
lean_object* v___x_2918_; 
lean_dec(v___x_2851_);
lean_dec_ref(v_array_2840_);
lean_dec(v_length_2838_);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v_it_x27_2853_);
lean_ctor_set(v___x_2918_, 1, v_buf_2837_);
return v___x_2918_;
}
v___jp_2854_:
{
lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = lean_nat_add(v_length_2838_, v___x_2850_);
lean_dec(v_length_2838_);
v___x_2856_ = lean_nat_dec_lt(v_maxLength_2836_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_byte_array_push(v_buf_2837_, v_c_2849_);
v_buf_2837_ = v___x_2857_;
v_length_2838_ = v___x_2855_;
v_a_2839_ = v_it_x27_2853_;
goto _start;
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_dec(v___x_2855_);
lean_dec_ref(v_buf_2837_);
v___x_2859_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2860_, 0, v_it_x27_2853_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
return v___x_2860_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2923_, lean_object* v_buf_2924_, lean_object* v_length_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2923_, v_buf_2924_, v_length_2925_, v_a_2926_);
lean_dec(v_maxLength_2923_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v_array_2933_; lean_object* v_idx_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v_array_2933_ = lean_ctor_get(v_a_2932_, 0);
v_idx_2934_ = lean_ctor_get(v_a_2932_, 1);
v___x_2935_ = lean_byte_array_size(v_array_2933_);
v___x_2936_ = lean_nat_dec_lt(v_idx_2934_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_box(0);
v___x_2938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2938_, 0, v_a_2932_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
return v___x_2938_;
}
else
{
uint8_t v___x_2939_; uint8_t v_got_2940_; uint8_t v___x_2941_; 
v___x_2939_ = 34;
v_got_2940_ = lean_byte_array_fget(v_array_2933_, v_idx_2934_);
v___x_2941_ = lean_uint8_dec_eq(v_got_2940_, v___x_2939_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2943_, 0, v_a_2932_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
return v___x_2943_;
}
else
{
lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2972_; 
lean_inc(v_idx_2934_);
lean_inc_ref(v_array_2933_);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_a_2932_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; lean_object* v_unused_2974_; 
v_unused_2973_ = lean_ctor_get(v_a_2932_, 1);
lean_dec(v_unused_2973_);
v_unused_2974_ = lean_ctor_get(v_a_2932_, 0);
lean_dec(v_unused_2974_);
v___x_2945_ = v_a_2932_;
v_isShared_2946_ = v_isSharedCheck_2972_;
goto v_resetjp_2944_;
}
else
{
lean_dec(v_a_2932_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2972_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2947_ = lean_unsigned_to_nat(1u);
v___x_2948_ = lean_nat_add(v_idx_2934_, v___x_2947_);
lean_dec(v_idx_2934_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_2948_);
v___x_2950_ = v___x_2945_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_array_2933_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = l_ByteArray_empty;
v___x_2952_ = lean_unsigned_to_nat(0u);
v___x_2953_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2931_, v___x_2951_, v___x_2952_, v___x_2950_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_pos_2954_; lean_object* v_res_2955_; uint8_t v___x_2956_; 
v_pos_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_pos_2954_);
v_res_2955_ = lean_ctor_get(v___x_2953_, 1);
lean_inc(v_res_2955_);
lean_dec_ref_known(v___x_2953_, 2);
v___x_2956_ = lean_string_validate_utf8(v_res_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_dec(v_res_2955_);
v___x_2957_ = lean_box(0);
v___x_2958_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2957_, v_pos_2954_);
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_string_from_utf8_unchecked(v_res_2955_);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
v___x_2961_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2960_, v_pos_2954_);
lean_dec_ref_known(v___x_2960_, 1);
return v___x_2961_;
}
}
else
{
lean_object* v_pos_2962_; lean_object* v_err_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
v_pos_2962_ = lean_ctor_get(v___x_2953_, 0);
v_err_2963_ = lean_ctor_get(v___x_2953_, 1);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2953_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_err_2963_);
lean_inc(v_pos_2962_);
lean_dec(v___x_2953_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_pos_2962_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_err_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_2975_, v_a_2976_);
lean_dec(v_maxLength_2975_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_2978_, lean_object* v_maxSpaceSequence_2979_, lean_object* v_x_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_pos_2983_; lean_object* v_pos_2987_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v_snd_2992_; lean_object* v_snd_2993_; uint8_t v___x_2994_; 
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2978_, v_maxSpaceSequence_2979_, v___x_2990_, v___y_2981_);
v_snd_2992_ = lean_ctor_get(v___x_2991_, 1);
lean_inc(v_snd_2992_);
lean_dec_ref(v___x_2991_);
v_snd_2993_ = lean_ctor_get(v_snd_2992_, 1);
v___x_2994_ = lean_unbox(v_snd_2993_);
if (v___x_2994_ == 0)
{
lean_object* v_fst_2995_; lean_object* v_array_2996_; lean_object* v_idx_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v_fst_2995_ = lean_ctor_get(v_snd_2992_, 0);
lean_inc(v_fst_2995_);
lean_dec(v_snd_2992_);
v_array_2996_ = lean_ctor_get(v_fst_2995_, 0);
v_idx_2997_ = lean_ctor_get(v_fst_2995_, 1);
v___x_2998_ = lean_byte_array_size(v_array_2996_);
v___x_2999_ = lean_nat_dec_lt(v_idx_2997_, v___x_2998_);
if (v___x_2999_ == 0)
{
v_pos_2983_ = v_fst_2995_;
goto v___jp_2982_;
}
else
{
uint8_t v___x_3000_; uint32_t v___x_3001_; uint32_t v___x_3002_; uint8_t v___x_3003_; 
v___x_3000_ = lean_byte_array_fget(v_array_2996_, v_idx_2997_);
v___x_3001_ = lean_uint8_to_uint32(v___x_3000_);
v___x_3002_ = 32;
v___x_3003_ = lean_uint32_dec_eq(v___x_3001_, v___x_3002_);
if (v___x_3003_ == 0)
{
uint32_t v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = 9;
v___x_3005_ = lean_uint32_dec_eq(v___x_3001_, v___x_3004_);
if (v___x_3005_ == 0)
{
v_pos_2983_ = v_fst_2995_;
goto v___jp_2982_;
}
else
{
v_pos_2987_ = v_fst_2995_;
goto v___jp_2986_;
}
}
else
{
v_pos_2987_ = v_fst_2995_;
goto v___jp_2986_;
}
}
}
else
{
lean_object* v_fst_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3014_; 
v_fst_3006_ = lean_ctor_get(v_snd_2992_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_snd_2992_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v_snd_2992_, 1);
lean_dec(v_unused_3015_);
v___x_3008_ = v_snd_2992_;
v_isShared_3009_ = v_isSharedCheck_3014_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_fst_3006_);
lean_dec(v_snd_2992_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3014_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3010_ = lean_box(0);
if (v_isShared_3009_ == 0)
{
lean_ctor_set_tag(v___x_3008_, 1);
lean_ctor_set(v___x_3008_, 1, v___x_3010_);
v___x_3012_ = v___x_3008_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_fst_3006_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
v___jp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v_pos_2983_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
return v___x_2985_;
}
v___jp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2989_, 0, v_pos_2987_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_3016_, lean_object* v_maxSpaceSequence_3017_, lean_object* v_x_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3016_, v_maxSpaceSequence_3017_, v_x_3018_, v___y_3019_);
lean_dec(v_maxSpaceSequence_3017_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_pos_3036_; lean_object* v_pos_3040_; lean_object* v___y_3044_; lean_object* v_pos_3045_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3077_; lean_object* v_pos_3078_; lean_object* v_res_3079_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v_lower_3085_; lean_object* v_upper_3086_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v_pos_3102_; lean_object* v_pos_3106_; lean_object* v_maxSpaceSequence_3109_; lean_object* v_maxChunkExtNameLength_3110_; lean_object* v_maxChunkExtValueLength_3111_; lean_object* v___f_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v_snd_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3403_; 
v_maxSpaceSequence_3109_ = lean_ctor_get(v_limits_3033_, 8);
v_maxChunkExtNameLength_3110_ = lean_ctor_get(v_limits_3033_, 11);
v_maxChunkExtValueLength_3111_ = lean_ctor_get(v_limits_3033_, 12);
v___f_3112_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3112_, v_maxSpaceSequence_3109_, v___x_3113_, v_a_3034_);
v_snd_3115_ = lean_ctor_get(v___x_3114_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v___x_3114_, 0);
lean_dec(v_unused_3404_);
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3403_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_snd_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3403_;
goto v_resetjp_3116_;
}
v___jp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3038_, 0, v_pos_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
return v___x_3038_;
}
v___jp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3042_, 0, v_pos_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
return v___x_3042_;
}
v___jp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___y_3044_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3048_, 0, v_pos_3045_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
return v___x_3048_;
}
v___jp_3049_:
{
if (lean_obj_tag(v___y_3051_) == 0)
{
lean_object* v_pos_3052_; lean_object* v_res_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3066_; 
v_pos_3052_ = lean_ctor_get(v___y_3051_, 0);
v_res_3053_ = lean_ctor_get(v___y_3051_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___y_3051_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3055_ = v___y_3051_;
v_isShared_3056_ = v_isSharedCheck_3066_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_res_3053_);
lean_inc(v_pos_3052_);
lean_dec(v___y_3051_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3066_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_3053_);
if (lean_obj_tag(v___x_3057_) == 1)
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___y_3050_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 1, v___x_3058_);
v___x_3060_ = v___x_3055_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_pos_3052_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
lean_dec(v___x_3057_);
lean_dec_ref(v___y_3050_);
v___x_3062_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_3056_ == 0)
{
lean_ctor_set_tag(v___x_3055_, 1);
lean_ctor_set(v___x_3055_, 1, v___x_3062_);
v___x_3064_ = v___x_3055_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_pos_3052_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v_pos_3067_; lean_object* v_err_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v___y_3050_);
v_pos_3067_ = lean_ctor_get(v___y_3051_, 0);
v_err_3068_ = lean_ctor_get(v___y_3051_, 1);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___y_3051_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___y_3051_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_err_3068_);
lean_inc(v_pos_3067_);
lean_dec(v___y_3051_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_pos_3067_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_err_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
v___jp_3076_:
{
lean_object* v___x_3080_; 
v___x_3080_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3079_, v_pos_3078_);
lean_dec(v_res_3079_);
v___y_3050_ = v___y_3077_;
v___y_3051_ = v___x_3080_;
goto v___jp_3049_;
}
v___jp_3081_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3087_ = l_ByteArray_toByteSlice(v___y_3084_, v_lower_3085_, v_upper_3086_);
v___x_3088_ = l_ByteSlice_toByteArray(v___x_3087_);
v___x_3089_ = lean_string_validate_utf8(v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
lean_dec_ref(v___x_3088_);
v___x_3090_ = lean_box(0);
v___y_3077_ = v___y_3083_;
v_pos_3078_ = v___y_3082_;
v_res_3079_ = v___x_3090_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_string_from_utf8_unchecked(v___x_3088_);
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
v___y_3077_ = v___y_3083_;
v_pos_3078_ = v___y_3082_;
v_res_3079_ = v___x_3092_;
goto v___jp_3076_;
}
}
v___jp_3093_:
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_nat_dec_le(v___y_3096_, v___y_3094_);
if (v___x_3100_ == 0)
{
lean_dec(v___y_3096_);
v___y_3082_ = v___y_3095_;
v___y_3083_ = v___y_3097_;
v___y_3084_ = v___y_3098_;
v_lower_3085_ = v___y_3099_;
v_upper_3086_ = v___y_3094_;
goto v___jp_3081_;
}
else
{
lean_dec(v___y_3094_);
v___y_3082_ = v___y_3095_;
v___y_3083_ = v___y_3097_;
v___y_3084_ = v___y_3098_;
v_lower_3085_ = v___y_3099_;
v_upper_3086_ = v___y_3096_;
goto v___jp_3081_;
}
}
v___jp_3101_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3104_, 0, v_pos_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
return v___x_3104_;
}
v___jp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_pos_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
return v___x_3108_;
}
v_resetjp_3116_:
{
lean_object* v_snd_3119_; uint8_t v___x_3120_; 
v_snd_3119_ = lean_ctor_get(v_snd_3115_, 1);
v___x_3120_ = lean_unbox(v_snd_3119_);
if (v___x_3120_ == 0)
{
lean_object* v_fst_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3391_; 
v_fst_3121_ = lean_ctor_get(v_snd_3115_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_snd_3115_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; 
v_unused_3392_ = lean_ctor_get(v_snd_3115_, 1);
lean_dec(v_unused_3392_);
v___x_3123_ = v_snd_3115_;
v_isShared_3124_ = v_isSharedCheck_3391_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_fst_3121_);
lean_dec(v_snd_3115_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3391_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v_array_3125_; lean_object* v_idx_3126_; lean_object* v___f_3127_; lean_object* v___y_3129_; lean_object* v_pos_3130_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v_pos_3165_; lean_object* v_array_3166_; lean_object* v_idx_3167_; lean_object* v_pos_3223_; lean_object* v_res_3224_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v_lower_3290_; lean_object* v_upper_3291_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v_pos_3306_; lean_object* v_pos_3339_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v_array_3125_ = lean_ctor_get(v_fst_3121_, 0);
v_idx_3126_ = lean_ctor_get(v_fst_3121_, 1);
v___f_3127_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_3383_ = lean_byte_array_size(v_array_3125_);
v___x_3384_ = lean_nat_dec_lt(v_idx_3126_, v___x_3383_);
if (v___x_3384_ == 0)
{
lean_inc(v_idx_3126_);
lean_inc_ref(v_array_3125_);
v_pos_3339_ = v_fst_3121_;
goto v___jp_3338_;
}
else
{
uint8_t v___x_3385_; uint32_t v___x_3386_; uint32_t v___x_3387_; uint8_t v___x_3388_; 
v___x_3385_ = lean_byte_array_fget(v_array_3125_, v_idx_3126_);
v___x_3386_ = lean_uint8_to_uint32(v___x_3385_);
v___x_3387_ = 32;
v___x_3388_ = lean_uint32_dec_eq(v___x_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
uint32_t v___x_3389_; uint8_t v___x_3390_; 
v___x_3389_ = 9;
v___x_3390_ = lean_uint32_dec_eq(v___x_3386_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_inc(v_idx_3126_);
lean_inc_ref(v_array_3125_);
v_pos_3339_ = v_fst_3121_;
goto v___jp_3338_;
}
else
{
lean_del_object(v___x_3123_);
lean_del_object(v___x_3117_);
v_pos_3036_ = v_fst_3121_;
goto v___jp_3035_;
}
}
else
{
lean_del_object(v___x_3123_);
lean_del_object(v___x_3117_);
v_pos_3036_ = v_fst_3121_;
goto v___jp_3035_;
}
}
v___jp_3128_:
{
lean_object* v___x_3131_; 
lean_inc_ref(v_pos_3130_);
v___x_3131_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_3111_, v_pos_3130_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_dec_ref(v_pos_3130_);
v___y_3050_ = v___y_3129_;
v___y_3051_ = v___x_3131_;
goto v___jp_3049_;
}
else
{
lean_object* v_pos_3132_; lean_object* v_idx_3133_; lean_object* v_array_3134_; lean_object* v_idx_3135_; uint8_t v___x_3136_; 
v_pos_3132_ = lean_ctor_get(v___x_3131_, 0);
v_idx_3133_ = lean_ctor_get(v_pos_3130_, 1);
lean_inc(v_idx_3133_);
lean_dec_ref(v_pos_3130_);
v_array_3134_ = lean_ctor_get(v_pos_3132_, 0);
v_idx_3135_ = lean_ctor_get(v_pos_3132_, 1);
v___x_3136_ = lean_nat_dec_eq(v_idx_3133_, v_idx_3135_);
lean_dec(v_idx_3133_);
if (v___x_3136_ == 0)
{
v___y_3050_ = v___y_3129_;
v___y_3051_ = v___x_3131_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3159_; 
lean_inc(v_pos_3132_);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; lean_object* v_unused_3161_; 
v_unused_3160_ = lean_ctor_get(v___x_3131_, 1);
lean_dec(v_unused_3160_);
v_unused_3161_ = lean_ctor_get(v___x_3131_, 0);
lean_dec(v_unused_3161_);
v___x_3138_ = v___x_3131_;
v_isShared_3139_ = v_isSharedCheck_3159_;
goto v_resetjp_3137_;
}
else
{
lean_dec(v___x_3131_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3159_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v_snd_3141_; lean_object* v_snd_3142_; uint8_t v___x_3143_; 
lean_inc(v_pos_3132_);
v___x_3140_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3127_, v_maxChunkExtValueLength_3111_, v___x_3113_, v_pos_3132_);
v_snd_3141_ = lean_ctor_get(v___x_3140_, 1);
lean_inc(v_snd_3141_);
v_snd_3142_ = lean_ctor_get(v_snd_3141_, 1);
v___x_3143_ = lean_unbox(v_snd_3142_);
if (v___x_3143_ == 0)
{
lean_object* v_fst_3144_; lean_object* v_fst_3145_; uint8_t v___x_3146_; 
v_fst_3144_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_fst_3144_);
lean_dec_ref(v___x_3140_);
v_fst_3145_ = lean_ctor_get(v_snd_3141_, 0);
lean_inc(v_fst_3145_);
lean_dec(v_snd_3141_);
v___x_3146_ = lean_nat_dec_eq(v_fst_3144_, v___x_3113_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
lean_inc(v_idx_3135_);
lean_inc_ref(v_array_3134_);
lean_del_object(v___x_3138_);
lean_dec(v_pos_3132_);
v___x_3147_ = lean_nat_add(v_idx_3135_, v_fst_3144_);
lean_dec(v_fst_3144_);
v___x_3148_ = lean_byte_array_size(v_array_3134_);
v___x_3149_ = lean_nat_dec_le(v_idx_3135_, v___x_3113_);
if (v___x_3149_ == 0)
{
v___y_3094_ = v___x_3148_;
v___y_3095_ = v_fst_3145_;
v___y_3096_ = v___x_3147_;
v___y_3097_ = v___y_3129_;
v___y_3098_ = v_array_3134_;
v___y_3099_ = v_idx_3135_;
goto v___jp_3093_;
}
else
{
lean_dec(v_idx_3135_);
v___y_3094_ = v___x_3148_;
v___y_3095_ = v_fst_3145_;
v___y_3096_ = v___x_3147_;
v___y_3097_ = v___y_3129_;
v___y_3098_ = v_array_3134_;
v___y_3099_ = v___x_3113_;
goto v___jp_3093_;
}
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
lean_dec(v_fst_3145_);
lean_dec(v_fst_3144_);
lean_dec_ref(v___y_3129_);
v___x_3150_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 1, v___x_3150_);
v___x_3152_ = v___x_3138_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_pos_3132_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
else
{
lean_object* v_fst_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
lean_dec_ref(v___x_3140_);
lean_dec(v_pos_3132_);
lean_dec_ref(v___y_3129_);
v_fst_3154_ = lean_ctor_get(v_snd_3141_, 0);
lean_inc(v_fst_3154_);
lean_dec(v_snd_3141_);
v___x_3155_ = lean_box(0);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 1, v___x_3155_);
lean_ctor_set(v___x_3138_, 0, v_fst_3154_);
v___x_3157_ = v___x_3138_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_fst_3154_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
}
v___jp_3162_:
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = lean_byte_array_size(v_array_3166_);
v___x_3169_ = lean_nat_dec_lt(v_idx_3167_, v___x_3168_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
lean_dec(v_idx_3167_);
lean_dec_ref(v_array_3166_);
lean_dec_ref(v___y_3163_);
v___x_3170_ = lean_box(0);
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 1);
lean_ctor_set(v___x_3123_, 1, v___x_3170_);
lean_ctor_set(v___x_3123_, 0, v_pos_3165_);
v___x_3172_ = v___x_3123_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_pos_3165_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
else
{
uint8_t v___x_3174_; uint8_t v_got_3175_; uint8_t v___x_3176_; 
v___x_3174_ = 61;
v_got_3175_ = lean_byte_array_fget(v_array_3166_, v_idx_3167_);
v___x_3176_ = lean_uint8_dec_eq(v_got_3175_, v___x_3174_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
lean_dec(v_idx_3167_);
lean_dec_ref(v_array_3166_);
lean_dec_ref(v___y_3163_);
v___x_3177_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 1);
lean_ctor_set(v___x_3123_, 1, v___x_3177_);
lean_ctor_set(v___x_3123_, 0, v_pos_3165_);
v___x_3179_ = v___x_3123_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_pos_3165_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3184_; 
lean_dec_ref(v_pos_3165_);
v___x_3181_ = lean_unsigned_to_nat(1u);
v___x_3182_ = lean_nat_add(v_idx_3167_, v___x_3181_);
lean_dec(v_idx_3167_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 1, v___x_3182_);
lean_ctor_set(v___x_3123_, 0, v_array_3166_);
v___x_3184_ = v___x_3123_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_array_3166_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3185_; 
v___x_3185_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3112_, v_maxSpaceSequence_3109_, v___y_3164_, v___x_3184_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_pos_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3210_; 
v_pos_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v___x_3185_, 1);
lean_dec(v_unused_3211_);
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3210_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_pos_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3210_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v_snd_3191_; lean_object* v_snd_3192_; uint8_t v___x_3193_; 
v___x_3190_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3112_, v_maxSpaceSequence_3109_, v___x_3113_, v_pos_3186_);
v_snd_3191_ = lean_ctor_get(v___x_3190_, 1);
lean_inc(v_snd_3191_);
lean_dec_ref(v___x_3190_);
v_snd_3192_ = lean_ctor_get(v_snd_3191_, 1);
v___x_3193_ = lean_unbox(v_snd_3192_);
if (v___x_3193_ == 0)
{
lean_object* v_fst_3194_; lean_object* v_array_3195_; lean_object* v_idx_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
lean_del_object(v___x_3188_);
v_fst_3194_ = lean_ctor_get(v_snd_3191_, 0);
lean_inc(v_fst_3194_);
lean_dec(v_snd_3191_);
v_array_3195_ = lean_ctor_get(v_fst_3194_, 0);
v_idx_3196_ = lean_ctor_get(v_fst_3194_, 1);
v___x_3197_ = lean_byte_array_size(v_array_3195_);
v___x_3198_ = lean_nat_dec_lt(v_idx_3196_, v___x_3197_);
if (v___x_3198_ == 0)
{
v___y_3129_ = v___y_3163_;
v_pos_3130_ = v_fst_3194_;
goto v___jp_3128_;
}
else
{
uint8_t v___x_3199_; uint32_t v___x_3200_; uint32_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3199_ = lean_byte_array_fget(v_array_3195_, v_idx_3196_);
v___x_3200_ = lean_uint8_to_uint32(v___x_3199_);
v___x_3201_ = 32;
v___x_3202_ = lean_uint32_dec_eq(v___x_3200_, v___x_3201_);
if (v___x_3202_ == 0)
{
uint32_t v___x_3203_; uint8_t v___x_3204_; 
v___x_3203_ = 9;
v___x_3204_ = lean_uint32_dec_eq(v___x_3200_, v___x_3203_);
if (v___x_3204_ == 0)
{
v___y_3129_ = v___y_3163_;
v_pos_3130_ = v_fst_3194_;
goto v___jp_3128_;
}
else
{
lean_dec_ref(v___y_3163_);
v_pos_3102_ = v_fst_3194_;
goto v___jp_3101_;
}
}
else
{
lean_dec_ref(v___y_3163_);
v_pos_3102_ = v_fst_3194_;
goto v___jp_3101_;
}
}
}
else
{
lean_object* v_fst_3205_; lean_object* v___x_3206_; lean_object* v___x_3208_; 
lean_dec_ref(v___y_3163_);
v_fst_3205_ = lean_ctor_get(v_snd_3191_, 0);
lean_inc(v_fst_3205_);
lean_dec(v_snd_3191_);
v___x_3206_ = lean_box(0);
if (v_isShared_3189_ == 0)
{
lean_ctor_set_tag(v___x_3188_, 1);
lean_ctor_set(v___x_3188_, 1, v___x_3206_);
lean_ctor_set(v___x_3188_, 0, v_fst_3205_);
v___x_3208_ = v___x_3188_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_fst_3205_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_pos_3212_; lean_object* v_err_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v___y_3163_);
v_pos_3212_ = lean_ctor_get(v___x_3185_, 0);
v_err_3213_ = lean_ctor_get(v___x_3185_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3185_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_err_3213_);
lean_inc(v_pos_3212_);
lean_dec(v___x_3185_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_pos_3212_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_err_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
}
}
v___jp_3222_:
{
lean_object* v___x_3225_; 
v___x_3225_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3224_, v_pos_3223_);
lean_dec(v_res_3224_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_pos_3226_; lean_object* v_res_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v_pos_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_pos_3226_);
v_res_3227_ = lean_ctor_get(v___x_3225_, 1);
lean_inc(v_res_3227_);
lean_dec_ref_known(v___x_3225_, 2);
v___x_3228_ = lean_box(0);
v___x_3229_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3112_, v_maxSpaceSequence_3109_, v___x_3228_, v_pos_3226_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_pos_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3267_; 
v_pos_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; 
v_unused_3268_ = lean_ctor_get(v___x_3229_, 1);
lean_dec(v_unused_3268_);
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3267_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_pos_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3267_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_3227_);
if (lean_obj_tag(v___x_3234_) == 1)
{
lean_object* v_val_3235_; lean_object* v_array_3236_; lean_object* v_idx_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v_val_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_val_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v_array_3236_ = lean_ctor_get(v_pos_3230_, 0);
v_idx_3237_ = lean_ctor_get(v_pos_3230_, 1);
v___x_3238_ = lean_byte_array_size(v_array_3236_);
v___x_3239_ = lean_nat_dec_lt(v_idx_3237_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_del_object(v___x_3232_);
lean_del_object(v___x_3123_);
v___y_3044_ = v_val_3235_;
v_pos_3045_ = v_pos_3230_;
goto v___jp_3043_;
}
else
{
uint8_t v___x_3240_; uint8_t v___x_3241_; uint8_t v___x_3242_; 
v___x_3240_ = lean_byte_array_fget(v_array_3236_, v_idx_3237_);
v___x_3241_ = 61;
v___x_3242_ = lean_uint8_dec_eq(v___x_3240_, v___x_3241_);
if (v___x_3242_ == 0)
{
lean_del_object(v___x_3232_);
lean_del_object(v___x_3123_);
v___y_3044_ = v_val_3235_;
v_pos_3045_ = v_pos_3230_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3243_; lean_object* v_snd_3244_; lean_object* v_snd_3245_; uint8_t v___x_3246_; 
v___x_3243_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3112_, v_maxSpaceSequence_3109_, v___x_3113_, v_pos_3230_);
v_snd_3244_ = lean_ctor_get(v___x_3243_, 1);
lean_inc(v_snd_3244_);
lean_dec_ref(v___x_3243_);
v_snd_3245_ = lean_ctor_get(v_snd_3244_, 1);
v___x_3246_ = lean_unbox(v_snd_3245_);
if (v___x_3246_ == 0)
{
lean_object* v_fst_3247_; lean_object* v_array_3248_; lean_object* v_idx_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; 
lean_del_object(v___x_3232_);
v_fst_3247_ = lean_ctor_get(v_snd_3244_, 0);
lean_inc(v_fst_3247_);
lean_dec(v_snd_3244_);
v_array_3248_ = lean_ctor_get(v_fst_3247_, 0);
v_idx_3249_ = lean_ctor_get(v_fst_3247_, 1);
v___x_3250_ = lean_byte_array_size(v_array_3248_);
v___x_3251_ = lean_nat_dec_lt(v_idx_3249_, v___x_3250_);
if (v___x_3251_ == 0)
{
lean_inc(v_idx_3249_);
lean_inc_ref(v_array_3248_);
v___y_3163_ = v_val_3235_;
v___y_3164_ = v___x_3228_;
v_pos_3165_ = v_fst_3247_;
v_array_3166_ = v_array_3248_;
v_idx_3167_ = v_idx_3249_;
goto v___jp_3162_;
}
else
{
uint8_t v___x_3252_; uint32_t v___x_3253_; uint32_t v___x_3254_; uint8_t v___x_3255_; 
v___x_3252_ = lean_byte_array_fget(v_array_3248_, v_idx_3249_);
v___x_3253_ = lean_uint8_to_uint32(v___x_3252_);
v___x_3254_ = 32;
v___x_3255_ = lean_uint32_dec_eq(v___x_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
uint32_t v___x_3256_; uint8_t v___x_3257_; 
v___x_3256_ = 9;
v___x_3257_ = lean_uint32_dec_eq(v___x_3253_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_inc(v_idx_3249_);
lean_inc_ref(v_array_3248_);
v___y_3163_ = v_val_3235_;
v___y_3164_ = v___x_3228_;
v_pos_3165_ = v_fst_3247_;
v_array_3166_ = v_array_3248_;
v_idx_3167_ = v_idx_3249_;
goto v___jp_3162_;
}
else
{
lean_dec(v_val_3235_);
lean_del_object(v___x_3123_);
v_pos_3106_ = v_fst_3247_;
goto v___jp_3105_;
}
}
else
{
lean_dec(v_val_3235_);
lean_del_object(v___x_3123_);
v_pos_3106_ = v_fst_3247_;
goto v___jp_3105_;
}
}
}
else
{
lean_object* v_fst_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
lean_dec(v_val_3235_);
lean_del_object(v___x_3123_);
v_fst_3258_ = lean_ctor_get(v_snd_3244_, 0);
lean_inc(v_fst_3258_);
lean_dec(v_snd_3244_);
v___x_3259_ = lean_box(0);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 1);
lean_ctor_set(v___x_3232_, 1, v___x_3259_);
lean_ctor_set(v___x_3232_, 0, v_fst_3258_);
v___x_3261_ = v___x_3232_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_fst_3258_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
lean_dec(v___x_3234_);
lean_del_object(v___x_3123_);
v___x_3263_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 1);
lean_ctor_set(v___x_3232_, 1, v___x_3263_);
v___x_3265_ = v___x_3232_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_pos_3230_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v_pos_3269_; lean_object* v_err_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec(v_res_3227_);
lean_del_object(v___x_3123_);
v_pos_3269_ = lean_ctor_get(v___x_3229_, 0);
v_err_3270_ = lean_ctor_get(v___x_3229_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3229_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_err_3270_);
lean_inc(v_pos_3269_);
lean_dec(v___x_3229_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_pos_3269_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_err_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v_pos_3278_; lean_object* v_err_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_del_object(v___x_3123_);
v_pos_3278_ = lean_ctor_get(v___x_3225_, 0);
v_err_3279_ = lean_ctor_get(v___x_3225_, 1);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3225_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_err_3279_);
lean_inc(v_pos_3278_);
lean_dec(v___x_3225_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_pos_3278_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_err_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
v___jp_3287_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
v___x_3292_ = l_ByteArray_toByteSlice(v___y_3289_, v_lower_3290_, v_upper_3291_);
v___x_3293_ = l_ByteSlice_toByteArray(v___x_3292_);
v___x_3294_ = lean_string_validate_utf8(v___x_3293_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; 
lean_dec_ref(v___x_3293_);
v___x_3295_ = lean_box(0);
v_pos_3223_ = v___y_3288_;
v_res_3224_ = v___x_3295_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = lean_string_from_utf8_unchecked(v___x_3293_);
v___x_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
v_pos_3223_ = v___y_3288_;
v_res_3224_ = v___x_3297_;
goto v___jp_3222_;
}
}
v___jp_3298_:
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_nat_dec_le(v___y_3302_, v___y_3301_);
if (v___x_3304_ == 0)
{
lean_dec(v___y_3302_);
v___y_3288_ = v___y_3299_;
v___y_3289_ = v___y_3300_;
v_lower_3290_ = v___y_3303_;
v_upper_3291_ = v___y_3301_;
goto v___jp_3287_;
}
else
{
lean_dec(v___y_3301_);
v___y_3288_ = v___y_3299_;
v___y_3289_ = v___y_3300_;
v_lower_3290_ = v___y_3303_;
v_upper_3291_ = v___y_3302_;
goto v___jp_3287_;
}
}
v___jp_3305_:
{
lean_object* v___x_3307_; lean_object* v_snd_3308_; lean_object* v_snd_3309_; uint8_t v___x_3310_; 
lean_inc_ref(v_pos_3306_);
v___x_3307_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3127_, v_maxChunkExtNameLength_3110_, v___x_3113_, v_pos_3306_);
v_snd_3308_ = lean_ctor_get(v___x_3307_, 1);
lean_inc(v_snd_3308_);
v_snd_3309_ = lean_ctor_get(v_snd_3308_, 1);
v___x_3310_ = lean_unbox(v_snd_3309_);
if (v___x_3310_ == 0)
{
lean_object* v_fst_3311_; lean_object* v_fst_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3326_; 
v_fst_3311_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_fst_3311_);
lean_dec_ref(v___x_3307_);
v_fst_3312_ = lean_ctor_get(v_snd_3308_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_snd_3308_);
if (v_isSharedCheck_3326_ == 0)
{
lean_object* v_unused_3327_; 
v_unused_3327_ = lean_ctor_get(v_snd_3308_, 1);
lean_dec(v_unused_3327_);
v___x_3314_ = v_snd_3308_;
v_isShared_3315_ = v_isSharedCheck_3326_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_fst_3312_);
lean_dec(v_snd_3308_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3326_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_nat_dec_eq(v_fst_3311_, v___x_3113_);
if (v___x_3316_ == 0)
{
lean_object* v_array_3317_; lean_object* v_idx_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
lean_del_object(v___x_3314_);
v_array_3317_ = lean_ctor_get(v_pos_3306_, 0);
lean_inc_ref(v_array_3317_);
v_idx_3318_ = lean_ctor_get(v_pos_3306_, 1);
lean_inc(v_idx_3318_);
lean_dec_ref(v_pos_3306_);
v___x_3319_ = lean_nat_add(v_idx_3318_, v_fst_3311_);
lean_dec(v_fst_3311_);
v___x_3320_ = lean_byte_array_size(v_array_3317_);
v___x_3321_ = lean_nat_dec_le(v_idx_3318_, v___x_3113_);
if (v___x_3321_ == 0)
{
v___y_3299_ = v_fst_3312_;
v___y_3300_ = v_array_3317_;
v___y_3301_ = v___x_3320_;
v___y_3302_ = v___x_3319_;
v___y_3303_ = v_idx_3318_;
goto v___jp_3298_;
}
else
{
lean_dec(v_idx_3318_);
v___y_3299_ = v_fst_3312_;
v___y_3300_ = v_array_3317_;
v___y_3301_ = v___x_3320_;
v___y_3302_ = v___x_3319_;
v___y_3303_ = v___x_3113_;
goto v___jp_3298_;
}
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_dec(v_fst_3312_);
lean_dec(v_fst_3311_);
lean_del_object(v___x_3123_);
v___x_3322_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 1);
lean_ctor_set(v___x_3314_, 1, v___x_3322_);
lean_ctor_set(v___x_3314_, 0, v_pos_3306_);
v___x_3324_ = v___x_3314_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_pos_3306_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_object* v_fst_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v___x_3307_);
lean_dec_ref(v_pos_3306_);
lean_del_object(v___x_3123_);
v_fst_3328_ = lean_ctor_get(v_snd_3308_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_snd_3308_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v_snd_3308_, 1);
lean_dec(v_unused_3337_);
v___x_3330_ = v_snd_3308_;
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_fst_3328_);
lean_dec(v_snd_3308_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3332_ = lean_box(0);
if (v_isShared_3331_ == 0)
{
lean_ctor_set_tag(v___x_3330_, 1);
lean_ctor_set(v___x_3330_, 1, v___x_3332_);
v___x_3334_ = v___x_3330_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_fst_3328_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
v___jp_3338_:
{
lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3340_ = lean_byte_array_size(v_array_3125_);
v___x_3341_ = lean_nat_dec_lt(v_idx_3126_, v___x_3340_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_dec(v_idx_3126_);
lean_dec_ref(v_array_3125_);
lean_del_object(v___x_3123_);
v___x_3342_ = lean_box(0);
if (v_isShared_3118_ == 0)
{
lean_ctor_set_tag(v___x_3117_, 1);
lean_ctor_set(v___x_3117_, 1, v___x_3342_);
lean_ctor_set(v___x_3117_, 0, v_pos_3339_);
v___x_3344_ = v___x_3117_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_pos_3339_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
else
{
uint8_t v___x_3346_; uint8_t v_got_3347_; uint8_t v___x_3348_; 
v___x_3346_ = 59;
v_got_3347_ = lean_byte_array_fget(v_array_3125_, v_idx_3126_);
v___x_3348_ = lean_uint8_dec_eq(v_got_3347_, v___x_3346_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
lean_dec(v_idx_3126_);
lean_dec_ref(v_array_3125_);
lean_del_object(v___x_3123_);
v___x_3349_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7));
if (v_isShared_3118_ == 0)
{
lean_ctor_set_tag(v___x_3117_, 1);
lean_ctor_set(v___x_3117_, 1, v___x_3349_);
lean_ctor_set(v___x_3117_, 0, v_pos_3339_);
v___x_3351_ = v___x_3117_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_pos_3339_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_dec_ref(v_pos_3339_);
v___x_3353_ = lean_unsigned_to_nat(1u);
v___x_3354_ = lean_nat_add(v_idx_3126_, v___x_3353_);
lean_dec(v_idx_3126_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3354_);
lean_ctor_set(v___x_3117_, 0, v_array_3125_);
v___x_3356_ = v___x_3117_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_array_3125_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; lean_object* v_snd_3358_; lean_object* v_snd_3359_; uint8_t v___x_3360_; 
v___x_3357_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3112_, v_maxSpaceSequence_3109_, v___x_3113_, v___x_3356_);
v_snd_3358_ = lean_ctor_get(v___x_3357_, 1);
lean_inc(v_snd_3358_);
lean_dec_ref(v___x_3357_);
v_snd_3359_ = lean_ctor_get(v_snd_3358_, 1);
v___x_3360_ = lean_unbox(v_snd_3359_);
if (v___x_3360_ == 0)
{
lean_object* v_fst_3361_; lean_object* v_array_3362_; lean_object* v_idx_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v_fst_3361_ = lean_ctor_get(v_snd_3358_, 0);
lean_inc(v_fst_3361_);
lean_dec(v_snd_3358_);
v_array_3362_ = lean_ctor_get(v_fst_3361_, 0);
v_idx_3363_ = lean_ctor_get(v_fst_3361_, 1);
v___x_3364_ = lean_byte_array_size(v_array_3362_);
v___x_3365_ = lean_nat_dec_lt(v_idx_3363_, v___x_3364_);
if (v___x_3365_ == 0)
{
v_pos_3306_ = v_fst_3361_;
goto v___jp_3305_;
}
else
{
uint8_t v___x_3366_; uint32_t v___x_3367_; uint32_t v___x_3368_; uint8_t v___x_3369_; 
v___x_3366_ = lean_byte_array_fget(v_array_3362_, v_idx_3363_);
v___x_3367_ = lean_uint8_to_uint32(v___x_3366_);
v___x_3368_ = 32;
v___x_3369_ = lean_uint32_dec_eq(v___x_3367_, v___x_3368_);
if (v___x_3369_ == 0)
{
uint32_t v___x_3370_; uint8_t v___x_3371_; 
v___x_3370_ = 9;
v___x_3371_ = lean_uint32_dec_eq(v___x_3367_, v___x_3370_);
if (v___x_3371_ == 0)
{
v_pos_3306_ = v_fst_3361_;
goto v___jp_3305_;
}
else
{
lean_del_object(v___x_3123_);
v_pos_3040_ = v_fst_3361_;
goto v___jp_3039_;
}
}
else
{
lean_del_object(v___x_3123_);
v_pos_3040_ = v_fst_3361_;
goto v___jp_3039_;
}
}
}
else
{
lean_object* v_fst_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3380_; 
lean_del_object(v___x_3123_);
v_fst_3372_ = lean_ctor_get(v_snd_3358_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_snd_3358_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v_snd_3358_, 1);
lean_dec(v_unused_3381_);
v___x_3374_ = v_snd_3358_;
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_fst_3372_);
lean_dec(v_snd_3358_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
v___x_3376_ = lean_box(0);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 1);
lean_ctor_set(v___x_3374_, 1, v___x_3376_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_fst_3372_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_fst_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3401_; 
lean_del_object(v___x_3117_);
v_fst_3393_ = lean_ctor_get(v_snd_3115_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_snd_3115_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v_snd_3115_, 1);
lean_dec(v_unused_3402_);
v___x_3395_ = v_snd_3115_;
v_isShared_3396_ = v_isSharedCheck_3401_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_fst_3393_);
lean_dec(v_snd_3115_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3401_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3397_ = lean_box(0);
if (v_isShared_3396_ == 0)
{
lean_ctor_set_tag(v___x_3395_, 1);
lean_ctor_set(v___x_3395_, 1, v___x_3397_);
v___x_3399_ = v___x_3395_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_fst_3393_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3405_, v_a_3406_);
lean_dec_ref(v_limits_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_pos_3411_; lean_object* v_err_3412_; lean_object* v___x_3428_; 
lean_inc_ref(v___y_3409_);
v___x_3428_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3408_, v___y_3409_);
if (lean_obj_tag(v___x_3428_) == 0)
{
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_pos_3429_; lean_object* v_res_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3438_; 
lean_dec_ref(v___y_3409_);
v_pos_3429_ = lean_ctor_get(v___x_3428_, 0);
v_res_3430_ = lean_ctor_get(v___x_3428_, 1);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3432_ = v___x_3428_;
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_res_3430_);
lean_inc(v_pos_3429_);
lean_dec(v___x_3428_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3434_, 0, v_res_3430_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3434_);
v___x_3436_ = v___x_3432_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_pos_3429_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
else
{
lean_object* v_pos_3439_; lean_object* v_err_3440_; 
v_pos_3439_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_pos_3439_);
v_err_3440_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_err_3440_);
lean_dec_ref_known(v___x_3428_, 2);
v_pos_3411_ = v_pos_3439_;
v_err_3412_ = v_err_3440_;
goto v___jp_3410_;
}
}
else
{
lean_object* v_err_3441_; 
v_err_3441_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_err_3441_);
lean_dec_ref_known(v___x_3428_, 2);
lean_inc_ref(v___y_3409_);
v_pos_3411_ = v___y_3409_;
v_err_3412_ = v_err_3441_;
goto v___jp_3410_;
}
v___jp_3410_:
{
lean_object* v_idx_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3426_; 
v_idx_3413_ = lean_ctor_get(v___y_3409_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___y_3409_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; 
v_unused_3427_ = lean_ctor_get(v___y_3409_, 0);
lean_dec(v_unused_3427_);
v___x_3415_ = v___y_3409_;
v_isShared_3416_ = v_isSharedCheck_3426_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_idx_3413_);
lean_dec(v___y_3409_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3426_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_idx_3417_; uint8_t v___x_3418_; 
v_idx_3417_ = lean_ctor_get(v_pos_3411_, 1);
v___x_3418_ = lean_nat_dec_eq(v_idx_3413_, v_idx_3417_);
lean_dec(v_idx_3413_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3420_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set_tag(v___x_3415_, 1);
lean_ctor_set(v___x_3415_, 1, v_err_3412_);
lean_ctor_set(v___x_3415_, 0, v_pos_3411_);
v___x_3420_ = v___x_3415_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_pos_3411_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_err_3412_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_dec(v_err_3412_);
v___x_3422_ = lean_box(0);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v___x_3422_);
lean_ctor_set(v___x_3415_, 0, v_pos_3411_);
v___x_3424_ = v___x_3415_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_pos_3411_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_3442_, v___y_3443_);
lean_dec_ref(v_limits_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v___x_3447_; 
v___x_3447_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_3446_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_pos_3448_; lean_object* v_res_3449_; lean_object* v_maxChunkExtensions_3450_; lean_object* v___f_3451_; lean_object* v___x_3452_; 
v_pos_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_pos_3448_);
v_res_3449_ = lean_ctor_get(v___x_3447_, 1);
lean_inc(v_res_3449_);
lean_dec_ref_known(v___x_3447_, 2);
v_maxChunkExtensions_3450_ = lean_ctor_get(v_limits_3445_, 10);
lean_inc(v_maxChunkExtensions_3450_);
v___f_3451_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3451_, 0, v_limits_3445_);
v___x_3452_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_3451_, v_maxChunkExtensions_3450_, v_pos_3448_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_pos_3453_; lean_object* v_res_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_pos_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_pos_3453_);
v_res_3454_ = lean_ctor_get(v___x_3452_, 1);
lean_inc(v_res_3454_);
lean_dec_ref_known(v___x_3452_, 2);
v___x_3455_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3456_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3455_, v_pos_3453_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_pos_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3465_; 
v_pos_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v___x_3456_, 1);
lean_dec(v_unused_3466_);
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3465_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_pos_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3465_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3461_, 0, v_res_3449_);
lean_ctor_set(v___x_3461_, 1, v_res_3454_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v___x_3461_);
v___x_3463_ = v___x_3459_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_pos_3457_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
else
{
lean_object* v_pos_3467_; lean_object* v_err_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec(v_res_3454_);
lean_dec(v_res_3449_);
v_pos_3467_ = lean_ctor_get(v___x_3456_, 0);
v_err_3468_ = lean_ctor_get(v___x_3456_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3456_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_err_3468_);
lean_inc(v_pos_3467_);
lean_dec(v___x_3456_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_pos_3467_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_err_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_pos_3476_; lean_object* v_err_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec(v_res_3449_);
v_pos_3476_ = lean_ctor_get(v___x_3452_, 0);
v_err_3477_ = lean_ctor_get(v___x_3452_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3452_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_err_3477_);
lean_inc(v_pos_3476_);
lean_dec(v___x_3452_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_pos_3476_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_err_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_pos_3485_; lean_object* v_err_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v_limits_3445_);
v_pos_3485_ = lean_ctor_get(v___x_3447_, 0);
v_err_3486_ = lean_ctor_get(v___x_3447_, 1);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3447_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_err_3486_);
lean_inc(v_pos_3485_);
lean_dec(v___x_3447_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_pos_3485_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_err_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx(lean_object* v_x_3494_){
_start:
{
if (lean_obj_tag(v_x_3494_) == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_unsigned_to_nat(0u);
return v___x_3495_;
}
else
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_unsigned_to_nat(1u);
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___boxed(lean_object* v_x_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx(v_x_3497_);
lean_dec_ref(v_x_3497_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_3499_, lean_object* v_k_3500_){
_start:
{
if (lean_obj_tag(v_t_3499_) == 0)
{
lean_object* v_data_3501_; lean_object* v___x_3502_; 
v_data_3501_ = lean_ctor_get(v_t_3499_, 0);
lean_inc_ref(v_data_3501_);
lean_dec_ref_known(v_t_3499_, 1);
v___x_3502_ = lean_apply_1(v_k_3500_, v_data_3501_);
return v___x_3502_;
}
else
{
lean_object* v_data_3503_; lean_object* v_remaining_3504_; lean_object* v___x_3505_; 
v_data_3503_ = lean_ctor_get(v_t_3499_, 0);
lean_inc_ref(v_data_3503_);
v_remaining_3504_ = lean_ctor_get(v_t_3499_, 1);
lean_inc(v_remaining_3504_);
lean_dec_ref_known(v_t_3499_, 2);
v___x_3505_ = lean_apply_2(v_k_3500_, v_data_3503_, v_remaining_3504_);
return v___x_3505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_3506_, lean_object* v_ctorIdx_3507_, lean_object* v_t_3508_, lean_object* v_h_3509_, lean_object* v_k_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3508_, v_k_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_3512_, lean_object* v_ctorIdx_3513_, lean_object* v_t_3514_, lean_object* v_h_3515_, lean_object* v_k_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_3512_, v_ctorIdx_3513_, v_t_3514_, v_h_3515_, v_k_3516_);
lean_dec(v_ctorIdx_3513_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_3518_, lean_object* v_complete_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3518_, v_complete_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_3521_, lean_object* v_t_3522_, lean_object* v_h_3523_, lean_object* v_complete_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3522_, v_complete_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_3526_, lean_object* v_incomplete_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3526_, v_incomplete_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_3529_, lean_object* v_t_3530_, lean_object* v_h_3531_, lean_object* v_incomplete_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3530_, v_incomplete_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_3534_, v_a_3535_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_res_3537_; lean_object* v_pos_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3578_; 
v_res_3537_ = lean_ctor_get(v___x_3536_, 1);
v_pos_3538_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3540_ = v___x_3536_;
v_isShared_3541_ = v_isSharedCheck_3578_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_res_3537_);
lean_inc(v_pos_3538_);
lean_dec(v___x_3536_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3578_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v_fst_3542_; lean_object* v_snd_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3577_; 
v_fst_3542_ = lean_ctor_get(v_res_3537_, 0);
v_snd_3543_ = lean_ctor_get(v_res_3537_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_res_3537_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3545_ = v_res_3537_;
v_isShared_3546_ = v_isSharedCheck_3577_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_snd_3543_);
lean_inc(v_fst_3542_);
lean_dec(v_res_3537_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3577_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3547_ = lean_unsigned_to_nat(0u);
v___x_3548_ = lean_nat_dec_eq(v_fst_3542_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_del_object(v___x_3540_);
v___x_3549_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_3542_, v_pos_3538_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_pos_3550_; lean_object* v_res_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3563_; 
v_pos_3550_ = lean_ctor_get(v___x_3549_, 0);
v_res_3551_ = lean_ctor_get(v___x_3549_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3553_ = v___x_3549_;
v_isShared_3554_ = v_isSharedCheck_3563_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_res_3551_);
lean_inc(v_pos_3550_);
lean_dec(v___x_3549_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3563_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 1, v_res_3551_);
lean_ctor_set(v___x_3545_, 0, v_snd_3543_);
v___x_3556_ = v___x_3545_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_snd_3543_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_res_3551_);
v___x_3556_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v_fst_3542_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 1, v___x_3558_);
v___x_3560_ = v___x_3553_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_pos_3550_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_object* v_pos_3564_; lean_object* v_err_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_del_object(v___x_3545_);
lean_dec(v_snd_3543_);
lean_dec(v_fst_3542_);
v_pos_3564_ = lean_ctor_get(v___x_3549_, 0);
v_err_3565_ = lean_ctor_get(v___x_3549_, 1);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3549_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_err_3565_);
lean_inc(v_pos_3564_);
lean_dec(v___x_3549_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_pos_3564_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_err_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3575_; 
lean_del_object(v___x_3545_);
lean_dec(v_snd_3543_);
lean_dec(v_fst_3542_);
v___x_3573_ = lean_box(0);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 1, v___x_3573_);
v___x_3575_ = v___x_3540_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_pos_3538_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
else
{
lean_object* v_pos_3579_; lean_object* v_err_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
v_pos_3579_ = lean_ctor_get(v___x_3536_, 0);
v_err_3580_ = lean_ctor_get(v___x_3536_, 1);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3536_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_err_3580_);
lean_inc(v_pos_3579_);
lean_dec(v___x_3536_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_pos_3579_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_err_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_3588_, lean_object* v_it_3589_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3590_ = l_ByteArray_Iterator_remainingBytes(v_it_3589_);
v___x_3591_ = lean_unsigned_to_nat(0u);
v___x_3592_ = lean_nat_dec_eq(v___x_3590_, v___x_3591_);
if (v___x_3592_ == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_nat_dec_lt(v___x_3590_, v_size_3588_);
if (v___x_3593_ == 0)
{
lean_object* v_array_3594_; lean_object* v_idx_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v___x_3590_);
v_array_3594_ = lean_ctor_get(v_it_3589_, 0);
v_idx_3595_ = lean_ctor_get(v_it_3589_, 1);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_it_3589_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3597_ = v_it_3589_;
v_isShared_3598_ = v_isSharedCheck_3614_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_idx_3595_);
lean_inc(v_array_3594_);
lean_dec(v_it_3589_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3614_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3599_ = lean_nat_add(v_idx_3595_, v_size_3588_);
lean_inc(v___x_3599_);
lean_inc_ref(v_array_3594_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 1, v___x_3599_);
v___x_3601_ = v___x_3597_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_array_3594_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v_lower_3603_; lean_object* v_upper_3604_; lean_object* v___x_3608_; lean_object* v___y_3610_; uint8_t v___x_3612_; 
v___x_3608_ = lean_byte_array_size(v_array_3594_);
v___x_3612_ = lean_nat_dec_le(v_idx_3595_, v___x_3591_);
if (v___x_3612_ == 0)
{
v___y_3610_ = v_idx_3595_;
goto v___jp_3609_;
}
else
{
lean_dec(v_idx_3595_);
v___y_3610_ = v___x_3591_;
goto v___jp_3609_;
}
v___jp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3605_ = l_ByteArray_toByteSlice(v_array_3594_, v_lower_3603_, v_upper_3604_);
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3601_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
return v___x_3607_;
}
v___jp_3609_:
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_nat_dec_le(v___x_3599_, v___x_3608_);
if (v___x_3611_ == 0)
{
lean_dec(v___x_3599_);
v_lower_3603_ = v___y_3610_;
v_upper_3604_ = v___x_3608_;
goto v___jp_3602_;
}
else
{
v_lower_3603_ = v___y_3610_;
v_upper_3604_ = v___x_3599_;
goto v___jp_3602_;
}
}
}
}
}
else
{
lean_object* v_array_3615_; lean_object* v_idx_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3636_; 
v_array_3615_ = lean_ctor_get(v_it_3589_, 0);
v_idx_3616_ = lean_ctor_get(v_it_3589_, 1);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_it_3589_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3618_ = v_it_3589_;
v_isShared_3619_ = v_isSharedCheck_3636_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_idx_3616_);
lean_inc(v_array_3615_);
lean_dec(v_it_3589_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3636_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
v___x_3620_ = lean_nat_add(v_idx_3616_, v___x_3590_);
lean_inc(v___x_3620_);
lean_inc_ref(v_array_3615_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 1, v___x_3620_);
v___x_3622_ = v___x_3618_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_array_3615_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v_lower_3624_; lean_object* v_upper_3625_; lean_object* v___x_3630_; lean_object* v___y_3632_; uint8_t v___x_3634_; 
v___x_3630_ = lean_byte_array_size(v_array_3615_);
v___x_3634_ = lean_nat_dec_le(v_idx_3616_, v___x_3591_);
if (v___x_3634_ == 0)
{
v___y_3632_ = v_idx_3616_;
goto v___jp_3631_;
}
else
{
lean_dec(v_idx_3616_);
v___y_3632_ = v___x_3591_;
goto v___jp_3631_;
}
v___jp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3626_ = l_ByteArray_toByteSlice(v_array_3615_, v_lower_3624_, v_upper_3625_);
v___x_3627_ = lean_nat_sub(v_size_3588_, v___x_3590_);
lean_dec(v___x_3590_);
v___x_3628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3622_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
return v___x_3629_;
}
v___jp_3631_:
{
uint8_t v___x_3633_; 
v___x_3633_ = lean_nat_dec_le(v___x_3620_, v___x_3630_);
if (v___x_3633_ == 0)
{
lean_dec(v___x_3620_);
v_lower_3624_ = v___y_3632_;
v_upper_3625_ = v___x_3630_;
goto v___jp_3623_;
}
else
{
v_lower_3624_ = v___y_3632_;
v_upper_3625_ = v___x_3620_;
goto v___jp_3623_;
}
}
}
}
}
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
lean_dec(v___x_3590_);
v___x_3637_ = lean_box(0);
v___x_3638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3638_, 0, v_it_3589_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3639_, lean_object* v_it_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3639_, v_it_3640_);
lean_dec(v_size_3639_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_res_3645_; 
v_res_3645_ = lean_ctor_get(v___x_3644_, 1);
if (lean_obj_tag(v_res_3645_) == 0)
{
lean_object* v_pos_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_inc_ref(v_res_3645_);
v_pos_3646_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_pos_3646_);
lean_dec_ref_known(v___x_3644_, 2);
v___x_3647_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3648_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3647_, v_pos_3646_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_pos_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
v_pos_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; 
v_unused_3657_ = lean_ctor_get(v___x_3648_, 1);
lean_dec(v_unused_3657_);
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_pos_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v_res_3645_);
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_pos_3649_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_res_3645_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
else
{
lean_object* v_pos_3658_; lean_object* v_err_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec_ref_known(v_res_3645_, 1);
v_pos_3658_ = lean_ctor_get(v___x_3648_, 0);
v_err_3659_ = lean_ctor_get(v___x_3648_, 1);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3648_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_err_3659_);
lean_inc(v_pos_3658_);
lean_dec(v___x_3648_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_pos_3658_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_err_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
return v___x_3644_;
}
}
else
{
return v___x_3644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3667_, v_a_3668_);
lean_dec(v_size_3667_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object* v_s_3670_, lean_object* v_p_3671_){
_start:
{
uint32_t v___y_3673_; lean_object* v___x_3678_; uint8_t v_decide_3679_; 
v___x_3678_ = lean_string_utf8_byte_size(v_s_3670_);
v_decide_3679_ = lean_nat_dec_eq(v_p_3671_, v___x_3678_);
if (v_decide_3679_ == 0)
{
uint32_t v___x_3680_; uint8_t v___y_3682_; uint32_t v___x_3685_; uint8_t v___x_3686_; 
v___x_3680_ = lean_string_utf8_get_fast(v_s_3670_, v_p_3671_);
v___x_3685_ = 65;
v___x_3686_ = lean_uint32_dec_le(v___x_3685_, v___x_3680_);
if (v___x_3686_ == 0)
{
v___y_3682_ = v___x_3686_;
goto v___jp_3681_;
}
else
{
uint32_t v___x_3687_; uint8_t v___x_3688_; 
v___x_3687_ = 90;
v___x_3688_ = lean_uint32_dec_le(v___x_3680_, v___x_3687_);
v___y_3682_ = v___x_3688_;
goto v___jp_3681_;
}
v___jp_3681_:
{
if (v___y_3682_ == 0)
{
v___y_3673_ = v___x_3680_;
goto v___jp_3672_;
}
else
{
uint32_t v___x_3683_; uint32_t v___x_3684_; 
v___x_3683_ = 32;
v___x_3684_ = lean_uint32_add(v___x_3680_, v___x_3683_);
v___y_3673_ = v___x_3684_;
goto v___jp_3672_;
}
}
}
else
{
lean_dec(v_p_3671_);
return v_s_3670_;
}
v___jp_3672_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_inc(v_p_3671_);
v___x_3674_ = lean_string_utf8_set(v_s_3670_, v_p_3671_, v___y_3673_);
v___x_3675_ = l_Char_utf8Size(v___y_3673_);
v___x_3676_ = lean_nat_add(v_p_3671_, v___x_3675_);
lean_dec(v___x_3675_);
lean_dec(v_p_3671_);
v_s_3670_ = v___x_3674_;
v_p_3671_ = v___x_3676_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3701_){
_start:
{
lean_object* v___x_3702_; lean_object* v_n_3703_; lean_object* v___x_3704_; uint8_t v___x_3705_; 
v___x_3702_ = lean_unsigned_to_nat(0u);
v_n_3703_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(v_name_3701_, v___x_3702_);
v___x_3704_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3705_ = lean_string_dec_eq(v_n_3703_, v___x_3704_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; uint8_t v___x_3707_; 
v___x_3706_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3707_ = lean_string_dec_eq(v_n_3703_, v___x_3706_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___x_3708_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3709_ = lean_string_dec_eq(v_n_3703_, v___x_3708_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3711_ = lean_string_dec_eq(v_n_3703_, v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3712_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3713_ = lean_string_dec_eq(v_n_3703_, v___x_3712_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3714_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5));
v___x_3715_ = lean_string_dec_eq(v_n_3703_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3716_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6));
v___x_3717_ = lean_string_dec_eq(v_n_3703_, v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3718_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7));
v___x_3719_ = lean_string_dec_eq(v_n_3703_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8));
v___x_3721_ = lean_string_dec_eq(v_n_3703_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3722_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9));
v___x_3723_ = lean_string_dec_eq(v_n_3703_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10));
v___x_3725_ = lean_string_dec_eq(v_n_3703_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; uint8_t v___x_3727_; 
v___x_3726_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11));
v___x_3727_ = lean_string_dec_eq(v_n_3703_, v___x_3726_);
lean_dec_ref(v_n_3703_);
return v___x_3727_;
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3725_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3723_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3721_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3719_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3717_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3715_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3713_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3711_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3709_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3707_;
}
}
else
{
lean_dec_ref(v_n_3703_);
return v___x_3705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3728_){
_start:
{
uint8_t v_res_3729_; lean_object* v_r_3730_; 
v_res_3729_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3728_);
v_r_3730_ = lean_box(v_res_3729_);
return v_r_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3732_, v_a_3733_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_res_3735_; 
v_res_3735_ = lean_ctor_get(v___x_3734_, 1);
lean_inc(v_res_3735_);
if (lean_obj_tag(v_res_3735_) == 1)
{
lean_object* v_val_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3757_; 
v_val_3736_ = lean_ctor_get(v_res_3735_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_res_3735_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3738_ = v_res_3735_;
v_isShared_3739_ = v_isSharedCheck_3757_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_val_3736_);
lean_dec(v_res_3735_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3757_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v_pos_3740_; lean_object* v_fst_3741_; uint8_t v___x_3742_; 
v_pos_3740_ = lean_ctor_get(v___x_3734_, 0);
v_fst_3741_ = lean_ctor_get(v_val_3736_, 0);
lean_inc_n(v_fst_3741_, 2);
lean_dec(v_val_3736_);
v___x_3742_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3741_);
if (v___x_3742_ == 0)
{
lean_dec(v_fst_3741_);
lean_del_object(v___x_3738_);
return v___x_3734_;
}
else
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3754_; 
lean_inc(v_pos_3740_);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; lean_object* v_unused_3756_; 
v_unused_3755_ = lean_ctor_get(v___x_3734_, 1);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v___x_3734_, 0);
lean_dec(v_unused_3756_);
v___x_3744_ = v___x_3734_;
v_isShared_3745_ = v_isSharedCheck_3754_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v___x_3734_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3754_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3746_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3747_ = lean_string_append(v___x_3746_, v_fst_3741_);
lean_dec(v_fst_3741_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 0, v___x_3747_);
v___x_3749_ = v___x_3738_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set_tag(v___x_3744_, 1);
lean_ctor_set(v___x_3744_, 1, v___x_3749_);
v___x_3751_ = v___x_3744_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_pos_3740_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3735_);
return v___x_3734_;
}
}
else
{
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3758_, v_a_3759_);
lean_dec_ref(v_limits_3758_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v_maxTrailerHeaders_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v_maxTrailerHeaders_3763_ = lean_ctor_get(v_limits_3761_, 17);
lean_inc(v_maxTrailerHeaders_3763_);
v___x_3764_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3764_, 0, v_limits_3761_);
v___x_3765_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3764_, v_maxTrailerHeaders_3763_, v_a_3762_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_pos_3766_; lean_object* v_res_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v_pos_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_pos_3766_);
v_res_3767_ = lean_ctor_get(v___x_3765_, 1);
lean_inc(v_res_3767_);
lean_dec_ref_known(v___x_3765_, 2);
v___x_3768_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3769_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3768_, v_pos_3766_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_pos_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
v_pos_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; 
v_unused_3778_ = lean_ctor_get(v___x_3769_, 1);
lean_dec(v_unused_3778_);
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_pos_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v_res_3767_);
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_pos_3770_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_res_3767_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
else
{
lean_object* v_pos_3779_; lean_object* v_err_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v_res_3767_);
v_pos_3779_ = lean_ctor_get(v___x_3769_, 0);
v_err_3780_ = lean_ctor_get(v___x_3769_, 1);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3769_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_err_3780_);
lean_inc(v_pos_3779_);
lean_dec(v___x_3769_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_pos_3779_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_err_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
return v___x_3765_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3788_){
_start:
{
uint32_t v___x_3789_; uint8_t v___y_3791_; uint32_t v___x_3796_; uint8_t v___x_3797_; 
v___x_3789_ = lean_uint8_to_uint32(v_c_3788_);
v___x_3796_ = 33;
v___x_3797_ = lean_uint32_dec_le(v___x_3796_, v___x_3789_);
if (v___x_3797_ == 0)
{
v___y_3791_ = v___x_3797_;
goto v___jp_3790_;
}
else
{
uint32_t v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = 126;
v___x_3799_ = lean_uint32_dec_le(v___x_3789_, v___x_3798_);
v___y_3791_ = v___x_3799_;
goto v___jp_3790_;
}
v___jp_3790_:
{
if (v___y_3791_ == 0)
{
uint32_t v___x_3792_; uint8_t v___x_3793_; 
v___x_3792_ = 32;
v___x_3793_ = lean_uint32_dec_eq(v___x_3789_, v___x_3792_);
if (v___x_3793_ == 0)
{
uint32_t v___x_3794_; uint8_t v___x_3795_; 
v___x_3794_ = 9;
v___x_3795_ = lean_uint32_dec_eq(v___x_3789_, v___x_3794_);
return v___x_3795_;
}
else
{
return v___x_3793_;
}
}
else
{
return v___y_3791_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3800_){
_start:
{
uint8_t v_c_boxed_3801_; uint8_t v_res_3802_; lean_object* v_r_3803_; 
v_c_boxed_3801_ = lean_unbox(v_c_3800_);
v_res_3802_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3801_);
v_r_3803_ = lean_box(v_res_3802_);
return v_r_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v_maxReasonPhraseLength_3806_; lean_object* v___f_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v_snd_3810_; lean_object* v_snd_3811_; uint8_t v___x_3812_; 
v_maxReasonPhraseLength_3806_ = lean_ctor_get(v_limits_3804_, 16);
v___f_3807_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_3808_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3805_);
v___x_3809_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3807_, v_maxReasonPhraseLength_3806_, v___x_3808_, v_a_3805_);
v_snd_3810_ = lean_ctor_get(v___x_3809_, 1);
lean_inc(v_snd_3810_);
v_snd_3811_ = lean_ctor_get(v_snd_3810_, 1);
v___x_3812_ = lean_unbox(v_snd_3811_);
if (v___x_3812_ == 0)
{
lean_object* v_fst_3813_; lean_object* v_fst_3814_; lean_object* v_array_3815_; lean_object* v_idx_3816_; lean_object* v_lower_3818_; lean_object* v_upper_3819_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___y_3831_; uint8_t v___x_3833_; 
v_fst_3813_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_fst_3813_);
lean_dec_ref(v___x_3809_);
v_fst_3814_ = lean_ctor_get(v_snd_3810_, 0);
lean_inc(v_fst_3814_);
lean_dec(v_snd_3810_);
v_array_3815_ = lean_ctor_get(v_a_3805_, 0);
lean_inc_ref(v_array_3815_);
v_idx_3816_ = lean_ctor_get(v_a_3805_, 1);
lean_inc(v_idx_3816_);
lean_dec_ref(v_a_3805_);
v___x_3828_ = lean_nat_add(v_idx_3816_, v_fst_3813_);
lean_dec(v_fst_3813_);
v___x_3829_ = lean_byte_array_size(v_array_3815_);
v___x_3833_ = lean_nat_dec_le(v_idx_3816_, v___x_3808_);
if (v___x_3833_ == 0)
{
v___y_3831_ = v_idx_3816_;
goto v___jp_3830_;
}
else
{
lean_dec(v_idx_3816_);
v___y_3831_ = v___x_3808_;
goto v___jp_3830_;
}
v___jp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3820_ = l_ByteArray_toByteSlice(v_array_3815_, v_lower_3818_, v_upper_3819_);
v___x_3821_ = l_ByteSlice_toByteArray(v___x_3820_);
v___x_3822_ = lean_string_validate_utf8(v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
lean_dec_ref(v___x_3821_);
v___x_3823_ = lean_box(0);
v___x_3824_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3823_, v_fst_3814_);
return v___x_3824_;
}
else
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3825_ = lean_string_from_utf8_unchecked(v___x_3821_);
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
v___x_3827_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3826_, v_fst_3814_);
lean_dec_ref_known(v___x_3826_, 1);
return v___x_3827_;
}
}
v___jp_3830_:
{
uint8_t v___x_3832_; 
v___x_3832_ = lean_nat_dec_le(v___x_3828_, v___x_3829_);
if (v___x_3832_ == 0)
{
lean_dec(v___x_3828_);
v_lower_3818_ = v___y_3831_;
v_upper_3819_ = v___x_3829_;
goto v___jp_3817_;
}
else
{
v_lower_3818_ = v___y_3831_;
v_upper_3819_ = v___x_3828_;
goto v___jp_3817_;
}
}
}
else
{
lean_object* v_fst_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v___x_3809_);
lean_dec_ref(v_a_3805_);
v_fst_3834_ = lean_ctor_get(v_snd_3810_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_snd_3810_);
if (v_isSharedCheck_3842_ == 0)
{
lean_object* v_unused_3843_; 
v_unused_3843_ = lean_ctor_get(v_snd_3810_, 1);
lean_dec(v_unused_3843_);
v___x_3836_ = v_snd_3810_;
v_isShared_3837_ = v_isSharedCheck_3842_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_fst_3834_);
lean_dec(v_snd_3810_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3842_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3838_ = lean_box(0);
if (v_isShared_3837_ == 0)
{
lean_ctor_set_tag(v___x_3836_, 1);
lean_ctor_set(v___x_3836_, 1, v___x_3838_);
v___x_3840_ = v___x_3836_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_fst_3834_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3844_, lean_object* v_a_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3844_, v_a_3845_);
lean_dec_ref(v_limits_3844_);
return v_res_3846_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3847_){
_start:
{
if (lean_obj_tag(v_x_3847_) == 0)
{
uint8_t v___x_3848_; 
v___x_3848_ = 1;
return v___x_3848_;
}
else
{
lean_object* v_head_3849_; lean_object* v_tail_3850_; uint8_t v___y_3852_; uint32_t v___x_3854_; uint32_t v___x_3855_; uint8_t v___x_3856_; 
v_head_3849_ = lean_ctor_get(v_x_3847_, 0);
v_tail_3850_ = lean_ctor_get(v_x_3847_, 1);
v___x_3854_ = 9;
v___x_3855_ = lean_unbox_uint32(v_head_3849_);
v___x_3856_ = lean_uint32_dec_eq(v___x_3855_, v___x_3854_);
if (v___x_3856_ == 0)
{
uint32_t v___x_3857_; uint32_t v___x_3858_; uint8_t v___x_3859_; 
v___x_3857_ = 32;
v___x_3858_ = lean_unbox_uint32(v_head_3849_);
v___x_3859_ = lean_uint32_dec_eq(v___x_3858_, v___x_3857_);
if (v___x_3859_ == 0)
{
uint32_t v___x_3860_; uint32_t v___x_3861_; uint8_t v___x_3862_; 
v___x_3860_ = 33;
v___x_3861_ = lean_unbox_uint32(v_head_3849_);
v___x_3862_ = lean_uint32_dec_le(v___x_3860_, v___x_3861_);
if (v___x_3862_ == 0)
{
v___y_3852_ = v___x_3862_;
goto v___jp_3851_;
}
else
{
uint32_t v___x_3863_; uint32_t v___x_3864_; uint8_t v___x_3865_; 
v___x_3863_ = 126;
v___x_3864_ = lean_unbox_uint32(v_head_3849_);
v___x_3865_ = lean_uint32_dec_le(v___x_3864_, v___x_3863_);
v___y_3852_ = v___x_3865_;
goto v___jp_3851_;
}
}
else
{
v_x_3847_ = v_tail_3850_;
goto _start;
}
}
else
{
v_x_3847_ = v_tail_3850_;
goto _start;
}
v___jp_3851_:
{
if (v___y_3852_ == 0)
{
return v___y_3852_;
}
else
{
v_x_3847_ = v_tail_3850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3868_){
_start:
{
uint8_t v_res_3869_; lean_object* v_r_3870_; 
v_res_3869_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3868_);
lean_dec(v_x_3868_);
v_r_3870_ = lean_box(v_res_3869_);
return v_r_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___y_3877_; lean_object* v___y_3881_; lean_object* v_pos_3882_; lean_object* v_res_3883_; lean_object* v_array_3891_; lean_object* v_idx_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v_array_3891_ = lean_ctor_get(v_a_3875_, 0);
v_idx_3892_ = lean_ctor_get(v_a_3875_, 1);
v___x_3893_ = lean_byte_array_size(v_array_3891_);
v___x_3894_ = lean_nat_dec_lt(v_idx_3892_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = lean_box(0);
v___x_3896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3896_, 0, v_a_3875_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
return v___x_3896_;
}
else
{
uint8_t v_c_3897_; lean_object* v___x_3898_; uint8_t v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; uint8_t v___y_3904_; uint8_t v___y_3905_; uint8_t v___x_3961_; uint8_t v___x_3962_; uint8_t v___x_3963_; lean_object* v___y_3965_; uint8_t v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; uint8_t v___y_3969_; uint8_t v___y_3981_; 
v_c_3897_ = lean_byte_array_fget(v_array_3891_, v_idx_3892_);
v___x_3898_ = lean_unsigned_to_nat(48u);
v___x_3961_ = 48;
v___x_3962_ = lean_uint8_dec_le(v___x_3961_, v_c_3897_);
v___x_3963_ = 57;
if (v___x_3962_ == 0)
{
v___y_3981_ = v___x_3962_;
goto v___jp_3980_;
}
else
{
uint8_t v___x_4001_; 
v___x_4001_ = lean_uint8_dec_le(v_c_3897_, v___x_3963_);
v___y_3981_ = v___x_4001_;
goto v___jp_3980_;
}
v___jp_3899_:
{
if (v___y_3905_ == 0)
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
lean_dec(v___y_3901_);
lean_dec_ref(v_array_3891_);
v___x_3906_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___y_3903_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
return v___x_3907_;
}
else
{
lean_object* v___x_3908_; lean_object* v_it_x27_3909_; uint8_t v___x_3910_; 
lean_dec_ref(v___y_3903_);
v___x_3908_ = lean_nat_add(v___y_3901_, v___y_3902_);
lean_dec(v___y_3901_);
lean_inc(v___x_3908_);
lean_inc_ref(v_array_3891_);
v_it_x27_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3909_, 0, v_array_3891_);
lean_ctor_set(v_it_x27_3909_, 1, v___x_3908_);
v___x_3910_ = lean_nat_dec_lt(v___x_3908_, v___x_3893_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
lean_dec(v___x_3908_);
lean_dec_ref(v_array_3891_);
v___x_3911_ = lean_box(0);
v___x_3912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_it_x27_3909_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
return v___x_3912_;
}
else
{
uint8_t v___x_3913_; uint8_t v_got_3914_; uint8_t v___x_3915_; 
v___x_3913_ = 32;
v_got_3914_ = lean_byte_array_fget(v_array_3891_, v___x_3908_);
v___x_3915_ = lean_uint8_dec_eq(v_got_3914_, v___x_3913_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
lean_dec(v___x_3908_);
lean_dec_ref(v_array_3891_);
v___x_3916_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3917_, 0, v_it_x27_3909_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
return v___x_3917_;
}
else
{
uint32_t v___x_3918_; uint32_t v___x_3919_; uint32_t v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_dec_ref_known(v_it_x27_3909_, 2);
v___x_3918_ = lean_uint8_to_uint32(v_c_3897_);
v___x_3919_ = lean_uint8_to_uint32(v___y_3900_);
v___x_3920_ = lean_uint8_to_uint32(v___y_3904_);
v___x_3921_ = lean_uint32_to_nat(v___x_3918_);
v___x_3922_ = lean_nat_sub(v___x_3921_, v___x_3898_);
lean_dec(v___x_3921_);
v___x_3923_ = lean_unsigned_to_nat(100u);
v___x_3924_ = lean_nat_mul(v___x_3922_, v___x_3923_);
lean_dec(v___x_3922_);
v___x_3925_ = lean_uint32_to_nat(v___x_3919_);
v___x_3926_ = lean_nat_sub(v___x_3925_, v___x_3898_);
lean_dec(v___x_3925_);
v___x_3927_ = lean_unsigned_to_nat(10u);
v___x_3928_ = lean_nat_mul(v___x_3926_, v___x_3927_);
lean_dec(v___x_3926_);
v___x_3929_ = lean_nat_add(v___x_3924_, v___x_3928_);
lean_dec(v___x_3928_);
lean_dec(v___x_3924_);
v___x_3930_ = lean_uint32_to_nat(v___x_3920_);
v___x_3931_ = lean_nat_sub(v___x_3930_, v___x_3898_);
lean_dec(v___x_3930_);
v___x_3932_ = lean_nat_add(v___x_3929_, v___x_3931_);
lean_dec(v___x_3931_);
lean_dec(v___x_3929_);
v___x_3933_ = lean_nat_add(v___x_3908_, v___y_3902_);
lean_dec(v___x_3908_);
v___x_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3934_, 0, v_array_3891_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
v___x_3935_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3874_, v___x_3934_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_pos_3936_; lean_object* v_res_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v_pos_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_pos_3936_);
v_res_3937_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_res_3937_);
lean_dec_ref_known(v___x_3935_, 2);
v___x_3938_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3939_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3938_, v_pos_3936_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_pos_3940_; 
v_pos_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_pos_3940_);
lean_dec_ref_known(v___x_3939_, 2);
v___y_3881_ = v___x_3932_;
v_pos_3882_ = v_pos_3940_;
v_res_3883_ = v_res_3937_;
goto v___jp_3880_;
}
else
{
lean_object* v_pos_3941_; lean_object* v_err_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec(v_res_3937_);
lean_dec(v___x_3932_);
v_pos_3941_ = lean_ctor_get(v___x_3939_, 0);
v_err_3942_ = lean_ctor_get(v___x_3939_, 1);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3939_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_err_3942_);
lean_inc(v_pos_3941_);
lean_dec(v___x_3939_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_pos_3941_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_err_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_pos_3950_; lean_object* v_res_3951_; 
v_pos_3950_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_pos_3950_);
v_res_3951_ = lean_ctor_get(v___x_3935_, 1);
lean_inc(v_res_3951_);
lean_dec_ref_known(v___x_3935_, 2);
v___y_3881_ = v___x_3932_;
v_pos_3882_ = v_pos_3950_;
v_res_3883_ = v_res_3951_;
goto v___jp_3880_;
}
else
{
lean_object* v_pos_3952_; lean_object* v_err_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec(v___x_3932_);
v_pos_3952_ = lean_ctor_get(v___x_3935_, 0);
v_err_3953_ = lean_ctor_get(v___x_3935_, 1);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3935_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_err_3953_);
lean_inc(v_pos_3952_);
lean_dec(v___x_3935_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_pos_3952_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_err_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
}
}
}
}
v___jp_3964_:
{
if (v___y_3969_ == 0)
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec(v___y_3965_);
lean_dec_ref(v_array_3891_);
v___x_3970_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___y_3967_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
return v___x_3971_;
}
else
{
lean_object* v___x_3972_; lean_object* v_it_x27_3973_; uint8_t v___x_3974_; 
lean_dec_ref(v___y_3967_);
v___x_3972_ = lean_nat_add(v___y_3965_, v___y_3968_);
lean_dec(v___y_3965_);
lean_inc(v___x_3972_);
lean_inc_ref(v_array_3891_);
v_it_x27_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3973_, 0, v_array_3891_);
lean_ctor_set(v_it_x27_3973_, 1, v___x_3972_);
v___x_3974_ = lean_nat_dec_lt(v___x_3972_, v___x_3893_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
lean_dec(v___x_3972_);
lean_dec_ref(v_array_3891_);
v___x_3975_ = lean_box(0);
v___x_3976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3976_, 0, v_it_x27_3973_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
return v___x_3976_;
}
else
{
uint8_t v_c_3977_; uint8_t v___x_3978_; 
v_c_3977_ = lean_byte_array_fget(v_array_3891_, v___x_3972_);
v___x_3978_ = lean_uint8_dec_le(v___x_3961_, v_c_3977_);
if (v___x_3978_ == 0)
{
v___y_3900_ = v___y_3966_;
v___y_3901_ = v___x_3972_;
v___y_3902_ = v___y_3968_;
v___y_3903_ = v_it_x27_3973_;
v___y_3904_ = v_c_3977_;
v___y_3905_ = v___x_3978_;
goto v___jp_3899_;
}
else
{
uint8_t v___x_3979_; 
v___x_3979_ = lean_uint8_dec_le(v_c_3977_, v___x_3963_);
v___y_3900_ = v___y_3966_;
v___y_3901_ = v___x_3972_;
v___y_3902_ = v___y_3968_;
v___y_3903_ = v_it_x27_3973_;
v___y_3904_ = v_c_3977_;
v___y_3905_ = v___x_3979_;
goto v___jp_3899_;
}
}
}
}
v___jp_3980_:
{
if (v___y_3981_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3983_, 0, v_a_3875_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
return v___x_3983_;
}
else
{
lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3998_; 
lean_inc(v_idx_3892_);
lean_inc_ref(v_array_3891_);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_a_3875_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; lean_object* v_unused_4000_; 
v_unused_3999_ = lean_ctor_get(v_a_3875_, 1);
lean_dec(v_unused_3999_);
v_unused_4000_ = lean_ctor_get(v_a_3875_, 0);
lean_dec(v_unused_4000_);
v___x_3985_ = v_a_3875_;
v_isShared_3986_ = v_isSharedCheck_3998_;
goto v_resetjp_3984_;
}
else
{
lean_dec(v_a_3875_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3998_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v_it_x27_3990_; 
v___x_3987_ = lean_unsigned_to_nat(1u);
v___x_3988_ = lean_nat_add(v_idx_3892_, v___x_3987_);
lean_dec(v_idx_3892_);
lean_inc(v___x_3988_);
lean_inc_ref(v_array_3891_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 1, v___x_3988_);
v_it_x27_3990_ = v___x_3985_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_array_3891_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v___x_3988_);
v_it_x27_3990_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
uint8_t v___x_3991_; 
v___x_3991_ = lean_nat_dec_lt(v___x_3988_, v___x_3893_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
lean_dec(v___x_3988_);
lean_dec_ref(v_array_3891_);
v___x_3992_ = lean_box(0);
v___x_3993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3993_, 0, v_it_x27_3990_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
return v___x_3993_;
}
else
{
uint8_t v_c_3994_; uint8_t v___x_3995_; 
v_c_3994_ = lean_byte_array_fget(v_array_3891_, v___x_3988_);
v___x_3995_ = lean_uint8_dec_le(v___x_3961_, v_c_3994_);
if (v___x_3995_ == 0)
{
v___y_3965_ = v___x_3988_;
v___y_3966_ = v_c_3994_;
v___y_3967_ = v_it_x27_3990_;
v___y_3968_ = v___x_3987_;
v___y_3969_ = v___x_3995_;
goto v___jp_3964_;
}
else
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_uint8_dec_le(v_c_3994_, v___x_3963_);
v___y_3965_ = v___x_3988_;
v___y_3966_ = v_c_3994_;
v___y_3967_ = v_it_x27_3990_;
v___y_3968_ = v___x_3987_;
v___y_3969_ = v___x_3996_;
goto v___jp_3964_;
}
}
}
}
}
}
}
v___jp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_3879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___y_3877_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
return v___x_3879_;
}
v___jp_3880_:
{
lean_object* v___x_3884_; uint8_t v___x_3885_; 
lean_inc_ref(v_res_3883_);
v___x_3884_ = lean_string_data(v_res_3883_);
v___x_3885_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3884_);
lean_dec(v___x_3884_);
if (v___x_3885_ == 0)
{
lean_dec_ref(v_res_3883_);
lean_dec(v___y_3881_);
v___y_3877_ = v_pos_3882_;
goto v___jp_3876_;
}
else
{
lean_object* v___x_3886_; uint16_t v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_res_3883_);
v___x_3887_ = lean_uint16_of_nat(v___y_3881_);
lean_dec(v___y_3881_);
v___x_3888_ = l_Std_Http_Status_ofCode(v___x_3886_, v___x_3887_);
if (lean_obj_tag(v___x_3888_) == 1)
{
lean_object* v_val_3889_; lean_object* v___x_3890_; 
v_val_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v___x_3888_, 1);
v___x_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3890_, 0, v_pos_3882_);
lean_ctor_set(v___x_3890_, 1, v_val_3889_);
return v___x_3890_;
}
else
{
lean_dec(v___x_3888_);
v___y_3877_ = v_pos_3882_;
goto v___jp_3876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4002_, v_a_4003_);
lean_dec_ref(v_limits_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v___y_4008_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; uint8_t v___y_4015_; uint8_t v___y_4016_; lean_object* v_pos_4028_; lean_object* v_res_4029_; lean_object* v___x_4047_; 
v___x_4047_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4006_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_pos_4048_; lean_object* v_res_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4079_; 
v_pos_4048_ = lean_ctor_get(v___x_4047_, 0);
v_res_4049_ = lean_ctor_get(v___x_4047_, 1);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4051_ = v___x_4047_;
v_isShared_4052_ = v_isSharedCheck_4079_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_res_4049_);
lean_inc(v_pos_4048_);
lean_dec(v___x_4047_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4079_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v_array_4053_; lean_object* v_idx_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; 
v_array_4053_ = lean_ctor_get(v_pos_4048_, 0);
v_idx_4054_ = lean_ctor_get(v_pos_4048_, 1);
v___x_4055_ = lean_byte_array_size(v_array_4053_);
v___x_4056_ = lean_nat_dec_lt(v_idx_4054_, v___x_4055_);
if (v___x_4056_ == 0)
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
lean_dec(v_res_4049_);
v___x_4057_ = lean_box(0);
if (v_isShared_4052_ == 0)
{
lean_ctor_set_tag(v___x_4051_, 1);
lean_ctor_set(v___x_4051_, 1, v___x_4057_);
v___x_4059_ = v___x_4051_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_pos_4048_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
else
{
uint8_t v___x_4061_; uint8_t v_got_4062_; uint8_t v___x_4063_; 
v___x_4061_ = 32;
v_got_4062_ = lean_byte_array_fget(v_array_4053_, v_idx_4054_);
v___x_4063_ = lean_uint8_dec_eq(v_got_4062_, v___x_4061_);
if (v___x_4063_ == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4066_; 
lean_dec(v_res_4049_);
v___x_4064_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_4052_ == 0)
{
lean_ctor_set_tag(v___x_4051_, 1);
lean_ctor_set(v___x_4051_, 1, v___x_4064_);
v___x_4066_ = v___x_4051_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_pos_4048_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
else
{
lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4076_; 
lean_inc(v_idx_4054_);
lean_inc_ref(v_array_4053_);
lean_del_object(v___x_4051_);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_pos_4048_);
if (v_isSharedCheck_4076_ == 0)
{
lean_object* v_unused_4077_; lean_object* v_unused_4078_; 
v_unused_4077_ = lean_ctor_get(v_pos_4048_, 1);
lean_dec(v_unused_4077_);
v_unused_4078_ = lean_ctor_get(v_pos_4048_, 0);
lean_dec(v_unused_4078_);
v___x_4069_ = v_pos_4048_;
v_isShared_4070_ = v_isSharedCheck_4076_;
goto v_resetjp_4068_;
}
else
{
lean_dec(v_pos_4048_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4076_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4071_ = lean_unsigned_to_nat(1u);
v___x_4072_ = lean_nat_add(v_idx_4054_, v___x_4071_);
lean_dec(v_idx_4054_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 1, v___x_4072_);
v___x_4074_ = v___x_4069_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_array_4053_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
v_pos_4028_ = v___x_4074_;
v_res_4029_ = v_res_4049_;
goto v___jp_4027_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_pos_4080_; lean_object* v_res_4081_; 
v_pos_4080_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_pos_4080_);
v_res_4081_ = lean_ctor_get(v___x_4047_, 1);
lean_inc(v_res_4081_);
lean_dec_ref_known(v___x_4047_, 2);
v_pos_4028_ = v_pos_4080_;
v_res_4029_ = v_res_4081_;
goto v___jp_4027_;
}
else
{
lean_object* v_pos_4082_; lean_object* v_err_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
v_pos_4082_ = lean_ctor_get(v___x_4047_, 0);
v_err_4083_ = lean_ctor_get(v___x_4047_, 1);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4047_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_err_4083_);
lean_inc(v_pos_4082_);
lean_dec(v___x_4047_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_pos_4082_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_err_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
v___jp_4007_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_4010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___y_4008_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
return v___x_4010_;
}
v___jp_4011_:
{
if (v___y_4016_ == 0)
{
if (v___y_4015_ == 0)
{
lean_dec(v___y_4014_);
lean_dec(v___y_4012_);
v___y_4008_ = v___y_4013_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4017_; uint8_t v___x_4018_; 
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = lean_nat_dec_eq(v___y_4012_, v___x_4017_);
lean_dec(v___y_4012_);
if (v___x_4018_ == 0)
{
lean_dec(v___y_4014_);
v___y_4008_ = v___y_4013_;
goto v___jp_4007_;
}
else
{
uint8_t v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4019_ = 0;
v___x_4020_ = l_Std_Http_Headers_empty;
v___x_4021_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4021_, 0, v___y_4014_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
lean_ctor_set_uint8(v___x_4021_, sizeof(void*)*2, v___x_4019_);
v___x_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4022_, 0, v___y_4013_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
return v___x_4022_;
}
}
}
else
{
uint8_t v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_dec(v___y_4012_);
v___x_4023_ = 1;
v___x_4024_ = l_Std_Http_Headers_empty;
v___x_4025_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4025_, 0, v___y_4014_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
lean_ctor_set_uint8(v___x_4025_, sizeof(void*)*2, v___x_4023_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___y_4013_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
return v___x_4026_;
}
}
v___jp_4027_:
{
lean_object* v_fst_4030_; lean_object* v_snd_4031_; lean_object* v___x_4032_; 
v_fst_4030_ = lean_ctor_get(v_res_4029_, 0);
lean_inc(v_fst_4030_);
v_snd_4031_ = lean_ctor_get(v_res_4029_, 1);
lean_inc(v_snd_4031_);
lean_dec_ref(v_res_4029_);
v___x_4032_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4005_, v_pos_4028_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_pos_4033_; lean_object* v_res_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v_pos_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_pos_4033_);
v_res_4034_ = lean_ctor_get(v___x_4032_, 1);
lean_inc(v_res_4034_);
lean_dec_ref_known(v___x_4032_, 2);
v___x_4035_ = lean_unsigned_to_nat(1u);
v___x_4036_ = lean_nat_dec_eq(v_fst_4030_, v___x_4035_);
lean_dec(v_fst_4030_);
if (v___x_4036_ == 0)
{
v___y_4012_ = v_snd_4031_;
v___y_4013_ = v_pos_4033_;
v___y_4014_ = v_res_4034_;
v___y_4015_ = v___x_4036_;
v___y_4016_ = v___x_4036_;
goto v___jp_4011_;
}
else
{
uint8_t v___x_4037_; 
v___x_4037_ = lean_nat_dec_eq(v_snd_4031_, v___x_4035_);
v___y_4012_ = v_snd_4031_;
v___y_4013_ = v_pos_4033_;
v___y_4014_ = v_res_4034_;
v___y_4015_ = v___x_4036_;
v___y_4016_ = v___x_4037_;
goto v___jp_4011_;
}
}
else
{
lean_object* v_pos_4038_; lean_object* v_err_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v_snd_4031_);
lean_dec(v_fst_4030_);
v_pos_4038_ = lean_ctor_get(v___x_4032_, 0);
v_err_4039_ = lean_ctor_get(v___x_4032_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4032_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_err_4039_);
lean_inc(v_pos_4038_);
lean_dec(v___x_4032_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_pos_4038_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_err_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_4091_, v_a_4092_);
lean_dec_ref(v_limits_4091_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_pos_4097_; lean_object* v_res_4098_; lean_object* v___x_4128_; 
v___x_4128_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4095_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_pos_4129_; lean_object* v_res_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4160_; 
v_pos_4129_ = lean_ctor_get(v___x_4128_, 0);
v_res_4130_ = lean_ctor_get(v___x_4128_, 1);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4132_ = v___x_4128_;
v_isShared_4133_ = v_isSharedCheck_4160_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_res_4130_);
lean_inc(v_pos_4129_);
lean_dec(v___x_4128_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4160_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v_array_4134_; lean_object* v_idx_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; 
v_array_4134_ = lean_ctor_get(v_pos_4129_, 0);
v_idx_4135_ = lean_ctor_get(v_pos_4129_, 1);
v___x_4136_ = lean_byte_array_size(v_array_4134_);
v___x_4137_ = lean_nat_dec_lt(v_idx_4135_, v___x_4136_);
if (v___x_4137_ == 0)
{
lean_object* v___x_4138_; lean_object* v___x_4140_; 
lean_dec(v_res_4130_);
v___x_4138_ = lean_box(0);
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 1);
lean_ctor_set(v___x_4132_, 1, v___x_4138_);
v___x_4140_ = v___x_4132_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_pos_4129_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
else
{
uint8_t v___x_4142_; uint8_t v_got_4143_; uint8_t v___x_4144_; 
v___x_4142_ = 32;
v_got_4143_ = lean_byte_array_fget(v_array_4134_, v_idx_4135_);
v___x_4144_ = lean_uint8_dec_eq(v_got_4143_, v___x_4142_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
lean_dec(v_res_4130_);
v___x_4145_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 1);
lean_ctor_set(v___x_4132_, 1, v___x_4145_);
v___x_4147_ = v___x_4132_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_pos_4129_);
lean_ctor_set(v_reuseFailAlloc_4148_, 1, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
else
{
lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4157_; 
lean_inc(v_idx_4135_);
lean_inc_ref(v_array_4134_);
lean_del_object(v___x_4132_);
v_isSharedCheck_4157_ = !lean_is_exclusive(v_pos_4129_);
if (v_isSharedCheck_4157_ == 0)
{
lean_object* v_unused_4158_; lean_object* v_unused_4159_; 
v_unused_4158_ = lean_ctor_get(v_pos_4129_, 1);
lean_dec(v_unused_4158_);
v_unused_4159_ = lean_ctor_get(v_pos_4129_, 0);
lean_dec(v_unused_4159_);
v___x_4150_ = v_pos_4129_;
v_isShared_4151_ = v_isSharedCheck_4157_;
goto v_resetjp_4149_;
}
else
{
lean_dec(v_pos_4129_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4157_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4152_ = lean_unsigned_to_nat(1u);
v___x_4153_ = lean_nat_add(v_idx_4135_, v___x_4152_);
lean_dec(v_idx_4135_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 1, v___x_4153_);
v___x_4155_ = v___x_4150_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_array_4134_);
lean_ctor_set(v_reuseFailAlloc_4156_, 1, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
v_pos_4097_ = v___x_4155_;
v_res_4098_ = v_res_4130_;
goto v___jp_4096_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_pos_4161_; lean_object* v_res_4162_; 
v_pos_4161_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_pos_4161_);
v_res_4162_ = lean_ctor_get(v___x_4128_, 1);
lean_inc(v_res_4162_);
lean_dec_ref_known(v___x_4128_, 2);
v_pos_4097_ = v_pos_4161_;
v_res_4098_ = v_res_4162_;
goto v___jp_4096_;
}
else
{
lean_object* v_pos_4163_; lean_object* v_err_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
v_pos_4163_ = lean_ctor_get(v___x_4128_, 0);
v_err_4164_ = lean_ctor_get(v___x_4128_, 1);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4128_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_err_4164_);
lean_inc(v_pos_4163_);
lean_dec(v___x_4128_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_pos_4163_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v_err_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
v___jp_4096_:
{
lean_object* v_fst_4099_; lean_object* v_snd_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4127_; 
v_fst_4099_ = lean_ctor_get(v_res_4098_, 0);
v_snd_4100_ = lean_ctor_get(v_res_4098_, 1);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_res_4098_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4102_ = v_res_4098_;
v_isShared_4103_ = v_isSharedCheck_4127_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_snd_4100_);
lean_inc(v_fst_4099_);
lean_dec(v_res_4098_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4127_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4104_; 
v___x_4104_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4094_, v_pos_4097_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_pos_4105_; lean_object* v_res_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4117_; 
v_pos_4105_ = lean_ctor_get(v___x_4104_, 0);
v_res_4106_ = lean_ctor_get(v___x_4104_, 1);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4108_ = v___x_4104_;
v_isShared_4109_ = v_isSharedCheck_4117_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_res_4106_);
lean_inc(v_pos_4105_);
lean_dec(v___x_4104_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4117_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4110_; lean_object* v___x_4112_; 
v___x_4110_ = l_Std_Http_Version_ofNumber_x3f(v_fst_4099_, v_snd_4100_);
lean_dec(v_snd_4100_);
lean_dec(v_fst_4099_);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 1, v___x_4110_);
lean_ctor_set(v___x_4102_, 0, v_res_4106_);
v___x_4112_ = v___x_4102_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_res_4106_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v___x_4110_);
v___x_4112_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4114_; 
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 1, v___x_4112_);
v___x_4114_ = v___x_4108_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_pos_4105_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
lean_object* v_pos_4118_; lean_object* v_err_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_del_object(v___x_4102_);
lean_dec(v_snd_4100_);
lean_dec(v_fst_4099_);
v_pos_4118_ = lean_ctor_get(v___x_4104_, 0);
v_err_4119_ = lean_ctor_get(v___x_4104_, 1);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4104_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_err_4119_);
lean_inc(v_pos_4118_);
lean_dec(v___x_4104_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_pos_4118_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v_err_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_4172_, v_a_4173_);
lean_dec_ref(v_limits_4172_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object* v_limits_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v_maxTrailerHeaders_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_maxTrailerHeaders_4177_ = lean_ctor_get(v_limits_4175_, 17);
lean_inc(v_maxTrailerHeaders_4177_);
v___x_4178_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_4178_, 0, v_limits_4175_);
v___x_4179_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_4178_, v_maxTrailerHeaders_4177_, v_a_4176_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_pos_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v_pos_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_pos_4180_);
lean_dec_ref_known(v___x_4179_, 2);
v___x_4181_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4182_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4181_, v_pos_4180_);
return v___x_4182_;
}
else
{
lean_object* v_pos_4183_; lean_object* v_err_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
v_pos_4183_ = lean_ctor_get(v___x_4179_, 0);
v_err_4184_ = lean_ctor_get(v___x_4179_, 1);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4179_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_err_4184_);
lean_inc(v_pos_4183_);
lean_dec(v___x_4179_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_pos_4183_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v_err_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* initialize_Std_Http_Data(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
