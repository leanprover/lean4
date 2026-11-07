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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_toListImpl(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
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
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_ByteArray_Iterator_remainingBytes(lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x3f(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_Http_Version_ofNumber_x3f(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "too many items: "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " > "};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1_value;
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
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "chunk size too large"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__0_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expected hex digit"};
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object*);
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
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_value;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unrecognized method"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_value;
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "forbidden trailer field: "};
static const lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object*, lean_object*);
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
uint32_t v___x_2_; uint32_t v___x_8_; uint8_t v___x_9_; 
v___x_2_ = lean_uint8_to_uint32(v_c_1_);
v___x_8_ = 33;
v___x_9_ = lean_uint32_dec_le(v___x_8_, v___x_2_);
if (v___x_9_ == 0)
{
goto v___jp_3_;
}
else
{
uint32_t v___x_10_; uint8_t v___x_11_; 
v___x_10_ = 126;
v___x_11_ = lean_uint32_dec_le(v___x_2_, v___x_10_);
if (v___x_11_ == 0)
{
goto v___jp_3_;
}
else
{
return v___x_11_;
}
}
v___jp_3_:
{
uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 32;
v___x_5_ = lean_uint32_dec_eq(v___x_2_, v___x_4_);
if (v___x_5_ == 0)
{
uint32_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 9;
v___x_7_ = lean_uint32_dec_eq(v___x_2_, v___x_6_);
return v___x_7_;
}
else
{
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object* v_c_12_){
_start:
{
uint8_t v_c_boxed_13_; uint8_t v_res_14_; lean_object* v_r_15_; 
v_c_boxed_13_ = lean_unbox(v_c_12_);
v_res_14_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(v_c_boxed_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t v_c_16_){
_start:
{
uint32_t v___x_17_; uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_17_ = lean_uint8_to_uint32(v_c_16_);
v___x_23_ = 9;
v___x_24_ = lean_uint32_dec_eq(v___x_17_, v___x_23_);
if (v___x_24_ == 0)
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 32;
v___x_26_ = lean_uint32_dec_eq(v___x_17_, v___x_25_);
if (v___x_26_ == 0)
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 33;
v___x_28_ = lean_uint32_dec_eq(v___x_17_, v___x_27_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 35;
v___x_30_ = lean_uint32_dec_le(v___x_29_, v___x_17_);
if (v___x_30_ == 0)
{
goto v___jp_18_;
}
else
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 91;
v___x_32_ = lean_uint32_dec_le(v___x_17_, v___x_31_);
if (v___x_32_ == 0)
{
goto v___jp_18_;
}
else
{
return v___x_32_;
}
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
}
else
{
return v___x_24_;
}
v___jp_18_:
{
uint32_t v___x_19_; uint8_t v___x_20_; 
v___x_19_ = 93;
v___x_20_ = lean_uint32_dec_le(v___x_19_, v___x_17_);
if (v___x_20_ == 0)
{
return v___x_20_;
}
else
{
uint32_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 126;
v___x_22_ = lean_uint32_dec_le(v___x_17_, v___x_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText___boxed(lean_object* v_c_33_){
_start:
{
uint8_t v_c_boxed_34_; uint8_t v_res_35_; lean_object* v_r_36_; 
v_c_boxed_34_ = lean_unbox(v_c_33_);
v_res_35_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(v_c_boxed_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t v_c_37_){
_start:
{
uint32_t v___x_38_; uint32_t v___x_39_; uint8_t v___x_40_; 
v___x_38_ = lean_uint8_to_uint32(v_c_37_);
v___x_39_ = 32;
v___x_40_ = lean_uint32_dec_eq(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
uint32_t v___x_41_; uint8_t v___x_42_; 
v___x_41_ = 9;
v___x_42_ = lean_uint32_dec_eq(v___x_38_, v___x_41_);
return v___x_42_;
}
else
{
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object* v_c_43_){
_start:
{
uint8_t v_c_boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_c_boxed_44_ = lean_unbox(v_c_43_);
v_res_45_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(v_c_boxed_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof___redArg(lean_object* v_p_47_, lean_object* v_it_48_){
_start:
{
lean_object* v___x_49_; 
lean_inc_ref(v_it_48_);
v___x_49_ = lean_apply_1(v_p_47_, v_it_48_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_pos_50_; lean_object* v_res_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_59_; 
lean_dec_ref(v_it_48_);
v_pos_50_ = lean_ctor_get(v___x_49_, 0);
v_res_51_ = lean_ctor_get(v___x_49_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_59_ == 0)
{
v___x_53_ = v___x_49_;
v_isShared_54_ = v_isSharedCheck_59_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_res_51_);
lean_inc(v_pos_50_);
lean_dec(v___x_49_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_59_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_res_51_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_55_);
v___x_57_ = v___x_53_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_pos_50_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_err_60_; 
v_err_60_ = lean_ctor_get(v___x_49_, 1);
lean_inc(v_err_60_);
if (lean_obj_tag(v_err_60_) == 0)
{
lean_object* v_pos_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec_ref(v_it_48_);
v_pos_61_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_68_ == 0)
{
lean_object* v_unused_69_; 
v_unused_69_ = lean_ctor_get(v___x_49_, 1);
lean_dec(v_unused_69_);
v___x_63_ = v___x_49_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_pos_61_);
lean_dec(v___x_49_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_pos_61_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_err_60_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
else
{
lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_77_; 
lean_dec(v_err_60_);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; lean_object* v_unused_79_; 
v_unused_78_ = lean_ctor_get(v___x_49_, 1);
lean_dec(v_unused_78_);
v_unused_79_ = lean_ctor_get(v___x_49_, 0);
lean_dec(v_unused_79_);
v___x_71_ = v___x_49_;
v_isShared_72_ = v_isSharedCheck_77_;
goto v_resetjp_70_;
}
else
{
lean_dec(v___x_49_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_77_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = lean_box(0);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 0);
lean_ctor_set(v___x_71_, 1, v___x_73_);
lean_ctor_set(v___x_71_, 0, v_it_48_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_it_48_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof(lean_object* v_00_u03b1_80_, lean_object* v_p_81_, lean_object* v_it_82_){
_start:
{
lean_object* v___x_83_; 
lean_inc_ref(v_it_82_);
v___x_83_ = lean_apply_1(v_p_81_, v_it_82_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_pos_84_; lean_object* v_res_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_93_; 
lean_dec_ref(v_it_82_);
v_pos_84_ = lean_ctor_get(v___x_83_, 0);
v_res_85_ = lean_ctor_get(v___x_83_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_93_ == 0)
{
v___x_87_ = v___x_83_;
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_res_85_);
lean_inc(v_pos_84_);
lean_dec(v___x_83_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_res_85_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v___x_89_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_pos_84_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
else
{
lean_object* v_err_94_; 
v_err_94_ = lean_ctor_get(v___x_83_, 1);
lean_inc(v_err_94_);
if (lean_obj_tag(v_err_94_) == 0)
{
lean_object* v_pos_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec_ref(v_it_82_);
v_pos_95_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v___x_83_, 1);
lean_dec(v_unused_103_);
v___x_97_ = v___x_83_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_pos_95_);
lean_dec(v___x_83_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_pos_95_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_err_94_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_111_; 
lean_dec(v_err_94_);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; lean_object* v_unused_113_; 
v_unused_112_ = lean_ctor_get(v___x_83_, 1);
lean_dec(v_unused_112_);
v_unused_113_ = lean_ctor_get(v___x_83_, 0);
lean_dec(v_unused_113_);
v___x_105_ = v___x_83_;
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
else
{
lean_dec(v___x_83_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_box(0);
if (v_isShared_106_ == 0)
{
lean_ctor_set_tag(v___x_105_, 0);
lean_ctor_set(v___x_105_, 1, v___x_107_);
lean_ctor_set(v___x_105_, 0, v_it_82_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_it_82_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object* v_parser_116_, lean_object* v_maxCount_117_, lean_object* v_acc_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_120_; 
lean_inc_ref(v_parser_116_);
lean_inc_ref(v_a_119_);
v___x_120_ = lean_apply_1(v_parser_116_, v_a_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_res_121_; 
v_res_121_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_res_121_);
if (lean_obj_tag(v_res_121_) == 0)
{
lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec(v_maxCount_117_);
lean_dec_ref(v_parser_116_);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; lean_object* v_unused_130_; 
v_unused_129_ = lean_ctor_get(v___x_120_, 1);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v___x_120_, 0);
lean_dec(v_unused_130_);
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v_acc_118_);
lean_ctor_set(v___x_123_, 0, v_a_119_);
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_119_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_acc_118_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_object* v_pos_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_157_; 
lean_dec_ref(v_a_119_);
v_pos_131_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_120_, 1);
lean_dec(v_unused_158_);
v___x_133_ = v___x_120_;
v_isShared_134_ = v_isSharedCheck_157_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_pos_131_);
lean_dec(v___x_120_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_157_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_val_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_156_; 
v_val_135_ = lean_ctor_get(v_res_121_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_res_121_);
if (v_isSharedCheck_156_ == 0)
{
v___x_137_ = v_res_121_;
v_isShared_138_ = v_isSharedCheck_156_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_val_135_);
lean_dec(v_res_121_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_156_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = lean_array_push(v_acc_118_, v_val_135_);
v___x_140_ = lean_array_get_size(v___x_139_);
v___x_141_ = lean_nat_dec_lt(v_maxCount_117_, v___x_140_);
if (v___x_141_ == 0)
{
lean_del_object(v___x_137_);
lean_del_object(v___x_133_);
v_acc_118_ = v___x_139_;
v_a_119_ = v_pos_131_;
goto _start;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
lean_dec_ref(v___x_139_);
lean_dec_ref(v_parser_116_);
v___x_143_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0));
v___x_144_ = l_Nat_reprFast(v___x_140_);
v___x_145_ = lean_string_append(v___x_143_, v___x_144_);
lean_dec_ref(v___x_144_);
v___x_146_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1));
v___x_147_ = lean_string_append(v___x_145_, v___x_146_);
v___x_148_ = l_Nat_reprFast(v_maxCount_117_);
v___x_149_ = lean_string_append(v___x_147_, v___x_148_);
lean_dec_ref(v___x_148_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_149_);
v___x_151_ = v___x_137_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_155_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 1);
lean_ctor_set(v___x_133_, 1, v___x_151_);
v___x_153_ = v___x_133_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_pos_131_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
}
else
{
lean_object* v_err_159_; 
lean_dec(v_maxCount_117_);
lean_dec_ref(v_parser_116_);
v_err_159_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_err_159_);
if (lean_obj_tag(v_err_159_) == 0)
{
lean_object* v_pos_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_a_119_);
lean_dec_ref(v_acc_118_);
v_pos_160_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v___x_120_, 1);
lean_dec(v_unused_168_);
v___x_162_ = v___x_120_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_pos_160_);
lean_dec(v___x_120_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_pos_160_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_err_159_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec(v_err_159_);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; lean_object* v_unused_177_; 
v_unused_176_ = lean_ctor_get(v___x_120_, 1);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v___x_120_, 0);
lean_dec(v_unused_177_);
v___x_170_ = v___x_120_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_dec(v___x_120_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 0);
lean_ctor_set(v___x_170_, 1, v_acc_118_);
lean_ctor_set(v___x_170_, 0, v_a_119_);
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_119_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_acc_118_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object* v_00_u03b1_178_, lean_object* v_parser_179_, lean_object* v_maxCount_180_, lean_object* v_acc_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_179_, v_maxCount_180_, v_acc_181_, v_a_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object* v_parser_186_, lean_object* v_maxCount_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0));
v___x_190_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_186_, v_maxCount_187_, v___x_189_, v_a_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object* v_00_u03b1_191_, lean_object* v_parser_192_, lean_object* v_maxCount_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v_parser_192_, v_maxCount_193_, v_a_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object* v_x_199_, lean_object* v_a_200_){
_start:
{
if (lean_obj_tag(v_x_199_) == 1)
{
lean_object* v_val_201_; lean_object* v___x_202_; 
v_val_201_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_val_201_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_a_200_);
lean_ctor_set(v___x_202_, 1, v_val_201_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1));
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v_a_200_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object* v_x_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_205_, v_a_206_);
lean_dec(v_x_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object* v_00_u03b1_208_, lean_object* v_x_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_209_, v_a_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object* v_00_u03b1_212_, lean_object* v_x_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(v_00_u03b1_212_, v_x_213_, v_a_214_);
lean_dec(v_x_213_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t v_c_216_){
_start:
{
uint32_t v___x_217_; uint32_t v___x_228_; uint8_t v___x_229_; 
v___x_217_ = lean_uint8_to_uint32(v_c_216_);
v___x_228_ = 33;
v___x_229_ = lean_uint32_dec_eq(v___x_217_, v___x_228_);
if (v___x_229_ == 0)
{
uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_230_ = 35;
v___x_231_ = lean_uint32_dec_eq(v___x_217_, v___x_230_);
if (v___x_231_ == 0)
{
uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 36;
v___x_233_ = lean_uint32_dec_eq(v___x_217_, v___x_232_);
if (v___x_233_ == 0)
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 37;
v___x_235_ = lean_uint32_dec_eq(v___x_217_, v___x_234_);
if (v___x_235_ == 0)
{
uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 38;
v___x_237_ = lean_uint32_dec_eq(v___x_217_, v___x_236_);
if (v___x_237_ == 0)
{
uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 39;
v___x_239_ = lean_uint32_dec_eq(v___x_217_, v___x_238_);
if (v___x_239_ == 0)
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 42;
v___x_241_ = lean_uint32_dec_eq(v___x_217_, v___x_240_);
if (v___x_241_ == 0)
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 43;
v___x_243_ = lean_uint32_dec_eq(v___x_217_, v___x_242_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 45;
v___x_245_ = lean_uint32_dec_eq(v___x_217_, v___x_244_);
if (v___x_245_ == 0)
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 46;
v___x_247_ = lean_uint32_dec_eq(v___x_217_, v___x_246_);
if (v___x_247_ == 0)
{
uint32_t v___x_248_; uint8_t v___x_249_; 
v___x_248_ = 94;
v___x_249_ = lean_uint32_dec_eq(v___x_217_, v___x_248_);
if (v___x_249_ == 0)
{
uint32_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 95;
v___x_251_ = lean_uint32_dec_eq(v___x_217_, v___x_250_);
if (v___x_251_ == 0)
{
uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 96;
v___x_253_ = lean_uint32_dec_eq(v___x_217_, v___x_252_);
if (v___x_253_ == 0)
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 124;
v___x_255_ = lean_uint32_dec_eq(v___x_217_, v___x_254_);
if (v___x_255_ == 0)
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 126;
v___x_257_ = lean_uint32_dec_eq(v___x_217_, v___x_256_);
if (v___x_257_ == 0)
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 48;
v___x_259_ = lean_uint32_dec_le(v___x_258_, v___x_217_);
if (v___x_259_ == 0)
{
goto v___jp_223_;
}
else
{
uint32_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = 57;
v___x_261_ = lean_uint32_dec_le(v___x_217_, v___x_260_);
if (v___x_261_ == 0)
{
goto v___jp_223_;
}
else
{
return v___x_261_;
}
}
}
else
{
return v___x_257_;
}
}
else
{
return v___x_255_;
}
}
else
{
return v___x_253_;
}
}
else
{
return v___x_251_;
}
}
else
{
return v___x_249_;
}
}
else
{
return v___x_247_;
}
}
else
{
return v___x_245_;
}
}
else
{
return v___x_243_;
}
}
else
{
return v___x_241_;
}
}
else
{
return v___x_239_;
}
}
else
{
return v___x_237_;
}
}
else
{
return v___x_235_;
}
}
else
{
return v___x_233_;
}
}
else
{
return v___x_231_;
}
}
else
{
return v___x_229_;
}
v___jp_218_:
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 97;
v___x_220_ = lean_uint32_dec_le(v___x_219_, v___x_217_);
if (v___x_220_ == 0)
{
return v___x_220_;
}
else
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 122;
v___x_222_ = lean_uint32_dec_le(v___x_217_, v___x_221_);
return v___x_222_;
}
}
v___jp_223_:
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 65;
v___x_225_ = lean_uint32_dec_le(v___x_224_, v___x_217_);
if (v___x_225_ == 0)
{
goto v___jp_218_;
}
else
{
uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 90;
v___x_227_ = lean_uint32_dec_le(v___x_217_, v___x_226_);
if (v___x_227_ == 0)
{
goto v___jp_218_;
}
else
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object* v_c_262_){
_start:
{
uint8_t v_c_boxed_263_; uint8_t v_res_264_; lean_object* v_r_265_; 
v_c_boxed_263_ = lean_unbox(v_c_262_);
v_res_264_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_boxed_263_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object* v_limit_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_snd_275_; lean_object* v_snd_276_; uint8_t v___x_277_; 
v___f_272_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_273_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_271_);
v___x_274_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_272_, v_limit_270_, v___x_273_, v_a_271_);
v_snd_275_ = lean_ctor_get(v___x_274_, 1);
lean_inc(v_snd_275_);
v_snd_276_ = lean_ctor_get(v_snd_275_, 1);
v___x_277_ = lean_unbox(v_snd_276_);
if (v___x_277_ == 0)
{
lean_object* v_fst_278_; lean_object* v_fst_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_307_; 
v_fst_278_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_fst_278_);
lean_dec_ref(v___x_274_);
v_fst_279_ = lean_ctor_get(v_snd_275_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_snd_275_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v_snd_275_, 1);
lean_dec(v_unused_308_);
v___x_281_ = v_snd_275_;
v_isShared_282_ = v_isSharedCheck_307_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_fst_279_);
lean_dec(v_snd_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_307_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; 
v___x_283_ = lean_nat_dec_eq(v_fst_278_, v___x_273_);
if (v___x_283_ == 0)
{
lean_object* v_array_284_; lean_object* v_idx_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_302_; 
lean_del_object(v___x_281_);
v_array_284_ = lean_ctor_get(v_a_271_, 0);
v_idx_285_ = lean_ctor_get(v_a_271_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_a_271_);
if (v_isSharedCheck_302_ == 0)
{
v___x_287_ = v_a_271_;
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_idx_285_);
lean_inc(v_array_284_);
lean_dec(v_a_271_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_lower_290_; lean_object* v_upper_291_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___y_299_; uint8_t v___x_301_; 
v___x_296_ = lean_nat_add(v_idx_285_, v_fst_278_);
lean_dec(v_fst_278_);
v___x_297_ = lean_byte_array_size(v_array_284_);
v___x_301_ = lean_nat_dec_le(v_idx_285_, v___x_273_);
if (v___x_301_ == 0)
{
v___y_299_ = v_idx_285_;
goto v___jp_298_;
}
else
{
lean_dec(v_idx_285_);
v___y_299_ = v___x_273_;
goto v___jp_298_;
}
v___jp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = l_ByteArray_toByteSlice(v_array_284_, v_lower_290_, v_upper_291_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_292_);
lean_ctor_set(v___x_287_, 0, v_fst_279_);
v___x_294_ = v___x_287_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_fst_279_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
v___jp_298_:
{
uint8_t v___x_300_; 
v___x_300_ = lean_nat_dec_le(v___x_296_, v___x_297_);
if (v___x_300_ == 0)
{
lean_dec(v___x_296_);
v_lower_290_ = v___y_299_;
v_upper_291_ = v___x_297_;
goto v___jp_289_;
}
else
{
v_lower_290_ = v___y_299_;
v_upper_291_ = v___x_296_;
goto v___jp_289_;
}
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_305_; 
lean_dec(v_fst_279_);
lean_dec(v_fst_278_);
v___x_303_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 1);
lean_ctor_set(v___x_281_, 1, v___x_303_);
lean_ctor_set(v___x_281_, 0, v_a_271_);
v___x_305_ = v___x_281_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_271_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v_fst_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_a_271_);
v_fst_309_ = lean_ctor_get(v_snd_275_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_snd_275_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_snd_275_, 1);
lean_dec(v_unused_318_);
v___x_311_ = v_snd_275_;
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_fst_309_);
lean_dec(v_snd_275_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_box(0);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 1);
lean_ctor_set(v___x_311_, 1, v___x_313_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_fst_309_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object* v_limit_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(v_limit_319_, v_a_320_);
lean_dec(v_limit_319_);
return v_res_321_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0));
v___x_324_ = lean_string_to_utf8(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_327_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_326_, v_a_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object* v_limits_331_, lean_object* v_a_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_array_334_; lean_object* v_idx_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_array_334_ = lean_ctor_get(v___y_333_, 0);
v_idx_335_ = lean_ctor_get(v___y_333_, 1);
v___x_336_ = lean_byte_array_size(v_array_334_);
v___x_337_ = lean_nat_dec_lt(v_idx_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___y_333_);
lean_ctor_set(v___x_338_, 1, v_a_332_);
return v___x_338_;
}
else
{
uint8_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_byte_array_fget(v_array_334_, v_idx_335_);
v___x_340_ = 13;
v___x_341_ = lean_uint8_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___y_333_);
lean_ctor_set(v___x_342_, 1, v_a_332_);
return v___x_342_;
}
else
{
lean_object* v_maxLeadingEmptyLines_343_; uint8_t v___x_344_; 
v_maxLeadingEmptyLines_343_ = lean_ctor_get(v_limits_331_, 9);
v___x_344_ = lean_nat_dec_le(v_maxLeadingEmptyLines_343_, v_a_332_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_346_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_345_, v___y_333_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_pos_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_pos_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_pos_347_);
lean_dec_ref_known(v___x_346_, 2);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_a_332_, v___x_348_);
lean_dec(v_a_332_);
v_a_332_ = v___x_349_;
v___y_333_ = v_pos_347_;
goto _start;
}
else
{
lean_object* v_pos_351_; lean_object* v_err_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_a_332_);
v_pos_351_ = lean_ctor_get(v___x_346_, 0);
v_err_352_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_346_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_err_352_);
lean_inc(v_pos_351_);
lean_dec(v___x_346_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_pos_351_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_err_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v_a_332_);
v___x_360_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1));
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v___y_333_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object* v_limits_362_, lean_object* v_a_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_362_, v_a_363_, v___y_364_);
lean_dec_ref(v_limits_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_count_368_; lean_object* v___x_369_; 
v_count_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_366_, v_count_368_, v_a_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_pos_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_pos_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v___x_369_, 1);
lean_dec(v_unused_379_);
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_pos_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_box(0);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_pos_370_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
lean_object* v_pos_380_; lean_object* v_err_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_pos_380_ = lean_ctor_get(v___x_369_, 0);
v_err_381_ = lean_ctor_get(v___x_369_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_369_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_err_381_);
lean_inc(v_pos_380_);
lean_dec(v___x_369_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_pos_380_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_err_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object* v_limits_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_389_, v_a_390_);
lean_dec_ref(v_limits_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_392_, lean_object* v_inst_393_, lean_object* v_a_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_392_, v_a_394_, v___y_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_397_, lean_object* v_inst_398_, lean_object* v_a_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_397_, v_inst_398_, v_a_399_, v___y_400_);
lean_dec_ref(v_limits_397_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_405_){
_start:
{
lean_object* v_array_406_; lean_object* v_idx_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_array_406_ = lean_ctor_get(v_a_405_, 0);
v_idx_407_ = lean_ctor_get(v_a_405_, 1);
v___x_408_ = lean_byte_array_size(v_array_406_);
v___x_409_ = lean_nat_dec_lt(v_idx_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_box(0);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v_a_405_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
return v___x_411_;
}
else
{
uint8_t v___x_412_; uint8_t v_got_413_; uint8_t v___x_414_; 
v___x_412_ = 32;
v_got_413_ = lean_byte_array_fget(v_array_406_, v_idx_407_);
v___x_414_ = lean_uint8_dec_eq(v_got_413_, v___x_412_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v_a_405_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
return v___x_416_;
}
else
{
lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_427_; 
lean_inc(v_idx_407_);
lean_inc_ref(v_array_406_);
v_isSharedCheck_427_ = !lean_is_exclusive(v_a_405_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; lean_object* v_unused_429_; 
v_unused_428_ = lean_ctor_get(v_a_405_, 1);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_a_405_, 0);
lean_dec(v_unused_429_);
v___x_418_ = v_a_405_;
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
else
{
lean_dec(v_a_405_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_add(v_idx_407_, v___x_420_);
lean_dec(v_idx_407_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v___x_421_);
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_array_406_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_426_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_box(0);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
return v___x_425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_pos_437_; lean_object* v_pos_441_; lean_object* v_maxSpaceSequence_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_snd_448_; lean_object* v_snd_449_; uint8_t v___x_450_; 
v_maxSpaceSequence_444_ = lean_ctor_get(v_limits_434_, 8);
v___x_445_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_445_, v_maxSpaceSequence_444_, v___x_446_, v_a_435_);
v_snd_448_ = lean_ctor_get(v___x_447_, 1);
lean_inc(v_snd_448_);
lean_dec_ref(v___x_447_);
v_snd_449_ = lean_ctor_get(v_snd_448_, 1);
v___x_450_ = lean_unbox(v_snd_449_);
if (v___x_450_ == 0)
{
lean_object* v_fst_451_; lean_object* v_array_452_; lean_object* v_idx_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_fst_451_ = lean_ctor_get(v_snd_448_, 0);
lean_inc(v_fst_451_);
lean_dec(v_snd_448_);
v_array_452_ = lean_ctor_get(v_fst_451_, 0);
v_idx_453_ = lean_ctor_get(v_fst_451_, 1);
v___x_454_ = lean_byte_array_size(v_array_452_);
v___x_455_ = lean_nat_dec_lt(v_idx_453_, v___x_454_);
if (v___x_455_ == 0)
{
v_pos_437_ = v_fst_451_;
goto v___jp_436_;
}
else
{
uint8_t v___x_456_; uint32_t v___x_457_; uint32_t v___x_458_; uint8_t v___x_459_; 
v___x_456_ = lean_byte_array_fget(v_array_452_, v_idx_453_);
v___x_457_ = lean_uint8_to_uint32(v___x_456_);
v___x_458_ = 32;
v___x_459_ = lean_uint32_dec_eq(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
uint32_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = 9;
v___x_461_ = lean_uint32_dec_eq(v___x_457_, v___x_460_);
if (v___x_461_ == 0)
{
v_pos_437_ = v_fst_451_;
goto v___jp_436_;
}
else
{
v_pos_441_ = v_fst_451_;
goto v___jp_440_;
}
}
else
{
v_pos_441_ = v_fst_451_;
goto v___jp_440_;
}
}
}
else
{
lean_object* v_fst_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_fst_462_ = lean_ctor_get(v_snd_448_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_snd_448_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_snd_448_, 1);
lean_dec(v_unused_471_);
v___x_464_ = v_snd_448_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_fst_462_);
lean_dec(v_snd_448_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_box(0);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 1);
lean_ctor_set(v___x_464_, 1, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_fst_462_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
v___jp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_pos_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
return v___x_439_;
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_443_, 0, v_pos_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_472_, v_a_473_);
lean_dec_ref(v_limits_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_476_){
_start:
{
lean_object* v_array_477_; lean_object* v_idx_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_array_477_ = lean_ctor_get(v_a_476_, 0);
v_idx_478_ = lean_ctor_get(v_a_476_, 1);
v___x_479_ = lean_byte_array_size(v_array_477_);
v___x_480_ = lean_nat_dec_lt(v_idx_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_box(0);
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v_a_476_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_538_; 
lean_inc(v_idx_478_);
lean_inc_ref(v_array_477_);
v_isSharedCheck_538_ = !lean_is_exclusive(v_a_476_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; lean_object* v_unused_540_; 
v_unused_539_ = lean_ctor_get(v_a_476_, 1);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_a_476_, 0);
lean_dec(v_unused_540_);
v___x_484_ = v_a_476_;
v_isShared_485_ = v_isSharedCheck_538_;
goto v_resetjp_483_;
}
else
{
lean_dec(v_a_476_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_538_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v_c_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_it_x27_490_; 
v_c_486_ = lean_byte_array_fget(v_array_477_, v_idx_478_);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_idx_478_, v___x_487_);
lean_dec(v_idx_478_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_488_);
v_it_x27_490_ = v___x_484_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_array_477_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_488_);
v_it_x27_490_ = v_reuseFailAlloc_537_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
uint8_t v___x_533_; uint8_t v___x_534_; 
v___x_533_ = 48;
v___x_534_ = lean_uint8_dec_le(v___x_533_, v_c_486_);
if (v___x_534_ == 0)
{
goto v___jp_528_;
}
else
{
uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 57;
v___x_536_ = lean_uint8_dec_le(v_c_486_, v___x_535_);
if (v___x_536_ == 0)
{
goto v___jp_528_;
}
else
{
goto v___jp_508_;
}
}
v___jp_491_:
{
uint8_t v___x_492_; uint8_t v___x_493_; uint8_t v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_492_ = 97;
v___x_493_ = lean_uint8_sub(v_c_486_, v___x_492_);
v___x_494_ = 10;
v___x_495_ = lean_uint8_add(v___x_493_, v___x_494_);
v___x_496_ = lean_box(v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v_it_x27_490_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
return v___x_497_;
}
v___jp_498_:
{
uint8_t v___x_499_; uint8_t v___x_500_; 
v___x_499_ = 65;
v___x_500_ = lean_uint8_dec_le(v___x_499_, v_c_486_);
if (v___x_500_ == 0)
{
goto v___jp_491_;
}
else
{
uint8_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = 70;
v___x_502_ = lean_uint8_dec_le(v_c_486_, v___x_501_);
if (v___x_502_ == 0)
{
goto v___jp_491_;
}
else
{
uint8_t v___x_503_; uint8_t v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_503_ = lean_uint8_sub(v_c_486_, v___x_499_);
v___x_504_ = 10;
v___x_505_ = lean_uint8_add(v___x_503_, v___x_504_);
v___x_506_ = lean_box(v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_it_x27_490_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
return v___x_507_;
}
}
}
v___jp_508_:
{
uint8_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = 48;
v___x_510_ = lean_uint8_dec_le(v___x_509_, v_c_486_);
if (v___x_510_ == 0)
{
goto v___jp_498_;
}
else
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = 57;
v___x_512_ = lean_uint8_dec_le(v_c_486_, v___x_511_);
if (v___x_512_ == 0)
{
goto v___jp_498_;
}
else
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = lean_uint8_sub(v_c_486_, v___x_509_);
v___x_514_ = lean_box(v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_it_x27_490_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
return v___x_515_;
}
}
}
v___jp_516_:
{
lean_object* v___x_517_; uint32_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_517_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0));
v___x_518_ = lean_uint8_to_uint32(v_c_486_);
v___x_519_ = l_Char_quote(v___x_518_);
v___x_520_ = lean_string_append(v___x_517_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v_it_x27_490_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
return v___x_522_;
}
v___jp_523_:
{
uint8_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 65;
v___x_525_ = lean_uint8_dec_le(v___x_524_, v_c_486_);
if (v___x_525_ == 0)
{
goto v___jp_516_;
}
else
{
uint8_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = 70;
v___x_527_ = lean_uint8_dec_le(v_c_486_, v___x_526_);
if (v___x_527_ == 0)
{
goto v___jp_516_;
}
else
{
goto v___jp_508_;
}
}
}
v___jp_528_:
{
uint8_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 97;
v___x_530_ = lean_uint8_dec_le(v___x_529_, v_c_486_);
if (v___x_530_ == 0)
{
goto v___jp_523_;
}
else
{
uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 102;
v___x_532_ = lean_uint8_dec_le(v_c_486_, v___x_531_);
if (v___x_532_ == 0)
{
goto v___jp_523_;
}
else
{
goto v___jp_508_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object* v_acc_547_, lean_object* v_count_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_550_; 
lean_inc_ref(v_a_549_);
v___x_550_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_549_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_pos_551_; lean_object* v_res_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_a_549_);
v_pos_551_ = lean_ctor_get(v___x_550_, 0);
v_res_552_ = lean_ctor_get(v___x_550_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_569_ == 0)
{
v___x_554_ = v___x_550_;
v_isShared_555_ = v_isSharedCheck_569_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_res_552_);
lean_inc(v_pos_551_);
lean_dec(v___x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_569_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_556_ = lean_unsigned_to_nat(16u);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_add(v_count_548_, v___x_557_);
lean_dec(v_count_548_);
v___x_559_ = lean_nat_dec_lt(v___x_556_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_del_object(v___x_554_);
v___x_560_ = lean_nat_mul(v_acc_547_, v___x_556_);
lean_dec(v_acc_547_);
v___x_561_ = lean_unbox(v_res_552_);
lean_dec(v_res_552_);
v___x_562_ = lean_uint8_to_nat(v___x_561_);
v___x_563_ = lean_nat_add(v___x_560_, v___x_562_);
lean_dec(v___x_560_);
v_acc_547_ = v___x_563_;
v_count_548_ = v___x_558_;
v_a_549_ = v_pos_551_;
goto _start;
}
else
{
lean_object* v___x_565_; lean_object* v___x_567_; 
lean_dec(v___x_558_);
lean_dec(v_res_552_);
lean_dec(v_acc_547_);
v___x_565_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 1, v___x_565_);
v___x_567_ = v___x_554_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_pos_551_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_object* v_err_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_595_; 
v_err_570_ = lean_ctor_get(v___x_550_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_550_, 0);
lean_dec(v_unused_596_);
v___x_572_ = v___x_550_;
v_isShared_573_ = v_isSharedCheck_595_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_err_570_);
lean_dec(v___x_550_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_595_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v_array_574_; lean_object* v_idx_575_; uint8_t v___x_576_; 
v_array_574_ = lean_ctor_get(v_a_549_, 0);
v_idx_575_ = lean_ctor_get(v_a_549_, 1);
v___x_576_ = lean_nat_dec_eq(v_idx_575_, v_idx_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v_count_548_);
lean_dec(v_acc_547_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_a_549_);
v___x_578_ = v___x_572_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_549_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_err_570_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
lean_object* v___x_580_; uint8_t v___x_581_; 
lean_dec(v_err_570_);
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_nat_dec_eq(v_count_548_, v___x_580_);
lean_dec(v_count_548_);
if (v___x_581_ == 0)
{
lean_object* v___x_583_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 0);
lean_ctor_set(v___x_572_, 1, v_acc_547_);
lean_ctor_set(v___x_572_, 0, v_a_549_);
v___x_583_ = v___x_572_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_549_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_acc_547_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
lean_object* v___x_585_; uint8_t v___x_586_; 
lean_dec(v_acc_547_);
v___x_585_ = lean_byte_array_size(v_array_574_);
v___x_586_ = lean_nat_dec_lt(v_idx_575_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_587_);
lean_ctor_set(v___x_572_, 0, v_a_549_);
v___x_589_ = v___x_572_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_549_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_591_);
lean_ctor_set(v___x_572_, 0, v_a_549_);
v___x_593_ = v___x_572_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_549_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_598_, v___x_598_, v_a_597_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_602_ = lean_string_to_utf8(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_611_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_610_, v_a_609_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_pos_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_673_; 
v_pos_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_611_, 1);
lean_dec(v_unused_674_);
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_673_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_pos_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_673_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_array_621_; lean_object* v_idx_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_array_621_ = lean_ctor_get(v_pos_612_, 0);
v_idx_622_ = lean_ctor_get(v_pos_612_, 1);
v___x_623_ = lean_byte_array_size(v_array_621_);
v___x_624_ = lean_nat_dec_lt(v_idx_622_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_del_object(v___x_614_);
v___x_625_ = lean_box(0);
v___x_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_626_, 0, v_pos_612_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
return v___x_626_;
}
else
{
uint8_t v_c_627_; uint8_t v___x_628_; uint8_t v___x_629_; 
v_c_627_ = lean_byte_array_fget(v_array_621_, v_idx_622_);
v___x_628_ = 48;
v___x_629_ = lean_uint8_dec_le(v___x_628_, v_c_627_);
if (v___x_629_ == 0)
{
goto v___jp_616_;
}
else
{
uint8_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 57;
v___x_631_ = lean_uint8_dec_le(v_c_627_, v___x_630_);
if (v___x_631_ == 0)
{
goto v___jp_616_;
}
else
{
lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_670_; 
lean_inc(v_idx_622_);
lean_inc_ref(v_array_621_);
lean_del_object(v___x_614_);
v_isSharedCheck_670_ = !lean_is_exclusive(v_pos_612_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_671_ = lean_ctor_get(v_pos_612_, 1);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_pos_612_, 0);
lean_dec(v_unused_672_);
v___x_633_ = v_pos_612_;
v_isShared_634_ = v_isSharedCheck_670_;
goto v_resetjp_632_;
}
else
{
lean_dec(v_pos_612_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_670_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_it_x27_638_; 
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_add(v_idx_622_, v___x_635_);
lean_dec(v_idx_622_);
lean_inc(v___x_636_);
lean_inc_ref(v_array_621_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_636_);
v_it_x27_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_array_621_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_636_);
v_it_x27_638_ = v_reuseFailAlloc_669_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_lt(v___x_636_, v___x_623_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v___x_636_);
lean_dec_ref(v_array_621_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v_it_x27_638_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
return v___x_641_;
}
else
{
uint8_t v___x_642_; uint8_t v_got_643_; uint8_t v___x_644_; 
v___x_642_ = 46;
v_got_643_ = lean_byte_array_fget(v_array_621_, v___x_636_);
v___x_644_ = lean_uint8_dec_eq(v_got_643_, v___x_642_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v___x_636_);
lean_dec_ref(v_array_621_);
v___x_645_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5));
v___x_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_646_, 0, v_it_x27_638_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_652_; 
lean_dec_ref(v_it_x27_638_);
v___x_647_ = lean_nat_add(v___x_636_, v___x_635_);
lean_dec(v___x_636_);
lean_inc(v___x_647_);
lean_inc_ref(v_array_621_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_array_621_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_652_ = lean_nat_dec_lt(v___x_647_, v___x_623_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v___x_647_);
lean_dec_ref(v_array_621_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_648_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
return v___x_654_;
}
else
{
uint8_t v_c_655_; uint8_t v___x_656_; 
v_c_655_ = lean_byte_array_fget(v_array_621_, v___x_647_);
v___x_656_ = lean_uint8_dec_le(v___x_628_, v_c_655_);
if (v___x_656_ == 0)
{
lean_dec(v___x_647_);
lean_dec_ref(v_array_621_);
goto v___jp_649_;
}
else
{
uint8_t v___x_657_; 
v___x_657_ = lean_uint8_dec_le(v_c_655_, v___x_630_);
if (v___x_657_ == 0)
{
lean_dec(v___x_647_);
lean_dec_ref(v_array_621_);
goto v___jp_649_;
}
else
{
lean_object* v___x_658_; uint32_t v___x_659_; lean_object* v___x_660_; lean_object* v_it_x27_661_; uint32_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec_ref_known(v___x_648_, 2);
v___x_658_ = lean_unsigned_to_nat(48u);
v___x_659_ = lean_uint8_to_uint32(v_c_627_);
v___x_660_ = lean_nat_add(v___x_647_, v___x_635_);
lean_dec(v___x_647_);
v_it_x27_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_661_, 0, v_array_621_);
lean_ctor_set(v_it_x27_661_, 1, v___x_660_);
v___x_662_ = lean_uint8_to_uint32(v_c_655_);
v___x_663_ = lean_uint32_to_nat(v___x_659_);
v___x_664_ = lean_nat_sub(v___x_663_, v___x_658_);
lean_dec(v___x_663_);
v___x_665_ = lean_uint32_to_nat(v___x_662_);
v___x_666_ = lean_nat_sub(v___x_665_, v___x_658_);
lean_dec(v___x_665_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_664_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_it_x27_661_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
return v___x_668_;
}
}
}
v___jp_649_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_648_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
return v___x_651_;
}
}
}
}
}
}
}
}
v___jp_616_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_615_ == 0)
{
lean_ctor_set_tag(v___x_614_, 1);
lean_ctor_set(v___x_614_, 1, v___x_617_);
v___x_619_ = v___x_614_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_pos_612_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_pos_675_; lean_object* v_err_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
v_pos_675_ = lean_ctor_get(v___x_611_, 0);
v_err_676_ = lean_ctor_get(v___x_611_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_611_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_err_676_);
lean_inc(v_pos_675_);
lean_dec(v___x_611_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_pos_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_err_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_684_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_res_686_; lean_object* v_pos_687_; lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_res_686_ = lean_ctor_get(v___x_685_, 1);
lean_inc(v_res_686_);
v_pos_687_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_pos_687_);
lean_dec_ref_known(v___x_685_, 2);
v_fst_688_ = lean_ctor_get(v_res_686_, 0);
lean_inc(v_fst_688_);
v_snd_689_ = lean_ctor_get(v_res_686_, 1);
lean_inc(v_snd_689_);
lean_dec(v_res_686_);
v___x_690_ = l_Std_Http_Version_ofNumber_x3f(v_fst_688_, v_snd_689_);
lean_dec(v_snd_689_);
lean_dec(v_fst_688_);
v___x_691_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_690_, v_pos_687_);
lean_dec(v___x_690_);
return v___x_691_;
}
else
{
lean_object* v_pos_692_; lean_object* v_err_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_pos_692_ = lean_ctor_get(v___x_685_, 0);
v_err_693_ = lean_ctor_get(v___x_685_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_685_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_err_693_);
lean_inc(v_pos_692_);
lean_dec(v___x_685_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_pos_692_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_err_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object* v_a_701_, lean_object* v_f_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_apply_1(v_a_701_, v___y_703_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_pos_705_; lean_object* v_res_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_pos_705_ = lean_ctor_get(v___x_704_, 0);
v_res_706_ = lean_ctor_get(v___x_704_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_714_ == 0)
{
v___x_708_ = v___x_704_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_res_706_);
lean_inc(v_pos_705_);
lean_dec(v___x_704_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_apply_1(v_f_702_, v_res_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_pos_705_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v_pos_715_; lean_object* v_err_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_f_702_);
v_pos_715_ = lean_ctor_get(v___x_704_, 0);
v_err_716_ = lean_ctor_get(v___x_704_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_704_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_err_716_);
lean_inc(v_pos_715_);
lean_dec(v___x_704_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_pos_715_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_err_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_a_726_, lean_object* v_f_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v_a_726_, v_f_727_, v___y_728_);
return v___x_729_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object* v_x_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = 8;
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object* v_x_732_){
_start:
{
uint8_t v_res_733_; lean_object* v_r_734_; 
v_res_733_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_732_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object* v_x_735_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = 9;
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object* v_x_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_737_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object* v_x_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = 7;
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object* v_x_742_){
_start:
{
uint8_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_742_);
v_r_744_ = lean_box(v_res_743_);
return v_r_744_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object* v_x_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = 32;
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object* v_x_747_){
_start:
{
uint8_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_747_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object* v_x_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = 0;
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object* v_x_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_752_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object* v_x_755_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = 28;
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object* v_x_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object* v_x_760_){
_start:
{
uint8_t v___x_761_; 
v___x_761_ = 31;
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object* v_x_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_762_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object* v_x_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = 1;
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object* v_x_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_767_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object* v_x_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = 2;
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object* v_x_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(v_x_772_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object* v_x_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = 5;
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object* v_x_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_777_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object* v_x_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = 3;
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object* v_x_785_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = 4;
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object* v_x_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object* v_x_790_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = 6;
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object* v_x_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_792_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object* v_x_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = 10;
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object* v_x_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_797_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object* v_x_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = 11;
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object* v_x_802_){
_start:
{
uint8_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_802_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object* v_x_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = 12;
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object* v_x_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_807_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object* v_x_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = 13;
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_812_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object* v_x_815_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = 14;
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object* v_x_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_817_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object* v_x_820_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = 15;
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_822_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object* v_x_825_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = 16;
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object* v_x_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_827_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object* v_x_830_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = 17;
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_832_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object* v_x_835_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = 18;
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object* v_x_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object* v_x_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = 19;
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object* v_x_842_){
_start:
{
uint8_t v_res_843_; lean_object* v_r_844_; 
v_res_843_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_842_);
v_r_844_ = lean_box(v_res_843_);
return v_r_844_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object* v_x_845_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = 20;
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object* v_x_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_847_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object* v_x_850_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = 21;
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object* v_x_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object* v_x_855_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = 23;
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object* v_x_857_){
_start:
{
uint8_t v_res_858_; lean_object* v_r_859_; 
v_res_858_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_857_);
v_r_859_ = lean_box(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object* v_x_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = 27;
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object* v_x_862_){
_start:
{
uint8_t v_res_863_; lean_object* v_r_864_; 
v_res_863_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_862_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object* v_x_865_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = 22;
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object* v_x_867_){
_start:
{
uint8_t v_res_868_; lean_object* v_r_869_; 
v_res_868_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_867_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object* v_x_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = 24;
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_872_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object* v_x_875_){
_start:
{
uint8_t v___x_876_; 
v___x_876_ = 25;
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_877_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object* v_x_880_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = 26;
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object* v_x_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_882_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object* v_x_885_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = 29;
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_887_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object* v_x_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = 30;
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object* v_x_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_892_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object* v_x_895_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = 33;
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object* v_x_897_){
_start:
{
uint8_t v_res_898_; lean_object* v_r_899_; 
v_res_898_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_897_);
v_r_899_ = lean_box(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object* v_x_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = 34;
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object* v_x_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_902_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object* v_x_905_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = 35;
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object* v_x_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_907_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object* v_x_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = 36;
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object* v_x_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_912_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object* v_x_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = 38;
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object* v_x_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_917_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object* v_x_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = 37;
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object* v_x_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_922_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object* v_x_925_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = 39;
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object* v_x_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_927_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___x_933_ = lean_string_to_utf8(v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2);
v___x_935_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5));
v___x_939_ = lean_string_to_utf8(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6);
v___x_941_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9));
v___x_945_ = lean_string_to_utf8(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10);
v___x_947_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13));
v___x_951_ = lean_string_to_utf8(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14);
v___x_953_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17));
v___x_957_ = lean_string_to_utf8(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18);
v___x_959_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21));
v___x_963_ = lean_string_to_utf8(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22);
v___x_965_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25));
v___x_969_ = lean_string_to_utf8(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26);
v___x_971_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29));
v___x_975_ = lean_string_to_utf8(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30);
v___x_977_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33));
v___x_981_ = lean_string_to_utf8(v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34);
v___x_983_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37));
v___x_987_ = lean_string_to_utf8(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38);
v___x_989_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41));
v___x_993_ = lean_string_to_utf8(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42);
v___x_995_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45));
v___x_999_ = lean_string_to_utf8(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46);
v___x_1001_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49));
v___x_1005_ = lean_string_to_utf8(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50);
v___x_1007_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53));
v___x_1011_ = lean_string_to_utf8(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54);
v___x_1013_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57));
v___x_1017_ = lean_string_to_utf8(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58);
v___x_1019_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61));
v___x_1023_ = lean_string_to_utf8(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62);
v___x_1025_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65));
v___x_1029_ = lean_string_to_utf8(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66);
v___x_1031_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69));
v___x_1035_ = lean_string_to_utf8(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70);
v___x_1037_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73));
v___x_1041_ = lean_string_to_utf8(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74);
v___x_1043_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77));
v___x_1047_ = lean_string_to_utf8(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78);
v___x_1049_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81));
v___x_1053_ = lean_string_to_utf8(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82);
v___x_1055_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85));
v___x_1059_ = lean_string_to_utf8(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86);
v___x_1061_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89));
v___x_1065_ = lean_string_to_utf8(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90);
v___x_1067_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93));
v___x_1071_ = lean_string_to_utf8(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94);
v___x_1073_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97));
v___x_1077_ = lean_string_to_utf8(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98);
v___x_1079_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101));
v___x_1083_ = lean_string_to_utf8(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102);
v___x_1085_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105));
v___x_1089_ = lean_string_to_utf8(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106);
v___x_1091_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109));
v___x_1095_ = lean_string_to_utf8(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110);
v___x_1097_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113));
v___x_1101_ = lean_string_to_utf8(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114);
v___x_1103_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117));
v___x_1107_ = lean_string_to_utf8(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118);
v___x_1109_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121));
v___x_1113_ = lean_string_to_utf8(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122);
v___x_1115_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125));
v___x_1119_ = lean_string_to_utf8(v___x_1118_);
return v___x_1119_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126);
v___x_1121_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129));
v___x_1125_ = lean_string_to_utf8(v___x_1124_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130);
v___x_1127_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133));
v___x_1131_ = lean_string_to_utf8(v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134);
v___x_1133_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137));
v___x_1137_ = lean_string_to_utf8(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138);
v___x_1139_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141));
v___x_1143_ = lean_string_to_utf8(v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142);
v___x_1145_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145));
v___x_1149_ = lean_string_to_utf8(v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146);
v___x_1151_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149));
v___x_1155_ = lean_string_to_utf8(v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150);
v___x_1157_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153));
v___x_1161_ = lean_string_to_utf8(v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154);
v___x_1163_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157));
v___x_1167_ = lean_string_to_utf8(v___x_1166_);
return v___x_1167_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158);
v___x_1169_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___f_1174_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0));
v___x_1175_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3);
lean_inc_ref(v_a_1173_);
v___x_1176_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1175_, v___f_1174_, v_a_1173_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1176_;
}
else
{
lean_object* v_err_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1332_; 
v_err_1177_ = lean_ctor_get(v___x_1176_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1176_, 0);
lean_dec(v_unused_1333_);
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1332_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_err_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1332_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_idx_1181_; uint8_t v___x_1182_; 
v_idx_1181_ = lean_ctor_get(v_a_1173_, 1);
v___x_1182_ = lean_nat_dec_eq(v_idx_1181_, v_idx_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1184_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_a_1173_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_err_1177_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
else
{
lean_object* v___f_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1179_);
lean_dec(v_err_1177_);
v___f_1186_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4));
v___x_1187_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7);
lean_inc_ref(v_a_1173_);
v___x_1188_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1187_, v___f_1186_, v_a_1173_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1188_;
}
else
{
lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref_known(v___x_1188_, 2);
v___f_1189_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8));
v___x_1190_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11);
lean_inc_ref(v_a_1173_);
v___x_1191_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1190_, v___f_1189_, v_a_1173_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1191_;
}
else
{
lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec_ref_known(v___x_1191_, 2);
v___f_1192_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12));
v___x_1193_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15);
lean_inc_ref(v_a_1173_);
v___x_1194_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1193_, v___f_1192_, v_a_1173_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1194_;
}
else
{
lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec_ref_known(v___x_1194_, 2);
v___f_1195_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16));
v___x_1196_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19);
lean_inc_ref(v_a_1173_);
v___x_1197_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1196_, v___f_1195_, v_a_1173_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1197_;
}
else
{
lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref_known(v___x_1197_, 2);
v___f_1198_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20));
v___x_1199_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23);
lean_inc_ref(v_a_1173_);
v___x_1200_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1199_, v___f_1198_, v_a_1173_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1200_;
}
else
{
lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec_ref_known(v___x_1200_, 2);
v___f_1201_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24));
v___x_1202_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27);
lean_inc_ref(v_a_1173_);
v___x_1203_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1202_, v___f_1201_, v_a_1173_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1203_;
}
else
{
lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec_ref_known(v___x_1203_, 2);
v___f_1204_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28));
v___x_1205_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31);
lean_inc_ref(v_a_1173_);
v___x_1206_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1205_, v___f_1204_, v_a_1173_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1206_;
}
else
{
lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref_known(v___x_1206_, 2);
v___f_1207_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32));
v___x_1208_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35);
lean_inc_ref(v_a_1173_);
v___x_1209_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1208_, v___f_1207_, v_a_1173_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1209_;
}
else
{
lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref_known(v___x_1209_, 2);
v___f_1210_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36));
v___x_1211_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39);
lean_inc_ref(v_a_1173_);
v___x_1212_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1211_, v___f_1210_, v_a_1173_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1212_;
}
else
{
lean_object* v___f_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref_known(v___x_1212_, 2);
v___f_1213_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40));
v___x_1214_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43);
lean_inc_ref(v_a_1173_);
v___x_1215_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1214_, v___f_1213_, v_a_1173_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1215_;
}
else
{
lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref_known(v___x_1215_, 2);
v___f_1216_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44));
v___x_1217_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47);
lean_inc_ref(v_a_1173_);
v___x_1218_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1217_, v___f_1216_, v_a_1173_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1218_;
}
else
{
lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref_known(v___x_1218_, 2);
v___f_1219_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48));
v___x_1220_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51);
lean_inc_ref(v_a_1173_);
v___x_1221_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1220_, v___f_1219_, v_a_1173_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1221_;
}
else
{
lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref_known(v___x_1221_, 2);
v___f_1222_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52));
v___x_1223_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55);
lean_inc_ref(v_a_1173_);
v___x_1224_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1223_, v___f_1222_, v_a_1173_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1224_;
}
else
{
lean_object* v___f_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref_known(v___x_1224_, 2);
v___f_1225_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56));
v___x_1226_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59);
lean_inc_ref(v_a_1173_);
v___x_1227_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1226_, v___f_1225_, v_a_1173_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1227_;
}
else
{
lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec_ref_known(v___x_1227_, 2);
v___f_1228_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60));
v___x_1229_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63);
lean_inc_ref(v_a_1173_);
v___x_1230_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1229_, v___f_1228_, v_a_1173_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1230_;
}
else
{
lean_object* v___f_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec_ref_known(v___x_1230_, 2);
v___f_1231_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64));
v___x_1232_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67);
lean_inc_ref(v_a_1173_);
v___x_1233_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1232_, v___f_1231_, v_a_1173_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1233_;
}
else
{
lean_object* v___f_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref_known(v___x_1233_, 2);
v___f_1234_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68));
v___x_1235_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71);
lean_inc_ref(v_a_1173_);
v___x_1236_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1235_, v___f_1234_, v_a_1173_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1236_;
}
else
{
lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec_ref_known(v___x_1236_, 2);
v___f_1237_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72));
v___x_1238_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75);
lean_inc_ref(v_a_1173_);
v___x_1239_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1238_, v___f_1237_, v_a_1173_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1239_;
}
else
{
lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec_ref_known(v___x_1239_, 2);
v___f_1240_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76));
v___x_1241_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79);
lean_inc_ref(v_a_1173_);
v___x_1242_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1241_, v___f_1240_, v_a_1173_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1242_;
}
else
{
lean_object* v___f_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref_known(v___x_1242_, 2);
v___f_1243_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80));
v___x_1244_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83);
lean_inc_ref(v_a_1173_);
v___x_1245_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1244_, v___f_1243_, v_a_1173_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1245_;
}
else
{
lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec_ref_known(v___x_1245_, 2);
v___f_1246_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84));
v___x_1247_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87);
lean_inc_ref(v_a_1173_);
v___x_1248_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1247_, v___f_1246_, v_a_1173_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1248_;
}
else
{
lean_object* v___f_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref_known(v___x_1248_, 2);
v___f_1249_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88));
v___x_1250_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91);
lean_inc_ref(v_a_1173_);
v___x_1251_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1250_, v___f_1249_, v_a_1173_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1251_;
}
else
{
lean_object* v___f_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref_known(v___x_1251_, 2);
v___f_1252_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92));
v___x_1253_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95);
lean_inc_ref(v_a_1173_);
v___x_1254_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1253_, v___f_1252_, v_a_1173_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1254_;
}
else
{
lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref_known(v___x_1254_, 2);
v___f_1255_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96));
v___x_1256_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99);
lean_inc_ref(v_a_1173_);
v___x_1257_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1256_, v___f_1255_, v_a_1173_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1257_;
}
else
{
lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1257_, 2);
v___f_1258_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100));
v___x_1259_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103);
lean_inc_ref(v_a_1173_);
v___x_1260_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1259_, v___f_1258_, v_a_1173_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1260_;
}
else
{
lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref_known(v___x_1260_, 2);
v___f_1261_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104));
v___x_1262_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107);
lean_inc_ref(v_a_1173_);
v___x_1263_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1262_, v___f_1261_, v_a_1173_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1263_;
}
else
{
lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref_known(v___x_1263_, 2);
v___f_1264_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108));
v___x_1265_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111);
lean_inc_ref(v_a_1173_);
v___x_1266_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1265_, v___f_1264_, v_a_1173_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1266_;
}
else
{
lean_object* v___f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref_known(v___x_1266_, 2);
v___f_1267_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112));
v___x_1268_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115);
lean_inc_ref(v_a_1173_);
v___x_1269_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1268_, v___f_1267_, v_a_1173_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1269_;
}
else
{
lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec_ref_known(v___x_1269_, 2);
v___f_1270_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116));
v___x_1271_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119);
lean_inc_ref(v_a_1173_);
v___x_1272_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1271_, v___f_1270_, v_a_1173_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1272_;
}
else
{
lean_object* v___f_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec_ref_known(v___x_1272_, 2);
v___f_1273_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120));
v___x_1274_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123);
lean_inc_ref(v_a_1173_);
v___x_1275_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1274_, v___f_1273_, v_a_1173_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1275_;
}
else
{
lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref_known(v___x_1275_, 2);
v___f_1276_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124));
v___x_1277_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127);
lean_inc_ref(v_a_1173_);
v___x_1278_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1277_, v___f_1276_, v_a_1173_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1278_;
}
else
{
lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref_known(v___x_1278_, 2);
v___f_1279_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128));
v___x_1280_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131);
lean_inc_ref(v_a_1173_);
v___x_1281_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1280_, v___f_1279_, v_a_1173_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1281_;
}
else
{
lean_object* v___f_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec_ref_known(v___x_1281_, 2);
v___f_1282_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132));
v___x_1283_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135);
lean_inc_ref(v_a_1173_);
v___x_1284_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1283_, v___f_1282_, v_a_1173_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1284_;
}
else
{
lean_object* v___f_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref_known(v___x_1284_, 2);
v___f_1285_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136));
v___x_1286_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139);
lean_inc_ref(v_a_1173_);
v___x_1287_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1286_, v___f_1285_, v_a_1173_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1287_;
}
else
{
lean_object* v___f_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec_ref_known(v___x_1287_, 2);
v___f_1288_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140));
v___x_1289_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143);
lean_inc_ref(v_a_1173_);
v___x_1290_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1289_, v___f_1288_, v_a_1173_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1290_;
}
else
{
lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec_ref_known(v___x_1290_, 2);
v___f_1291_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144));
v___x_1292_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147);
lean_inc_ref(v_a_1173_);
v___x_1293_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1292_, v___f_1291_, v_a_1173_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1293_;
}
else
{
lean_object* v___f_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref_known(v___x_1293_, 2);
v___f_1294_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148));
v___x_1295_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151);
lean_inc_ref(v_a_1173_);
v___x_1296_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1295_, v___f_1294_, v_a_1173_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1296_;
}
else
{
lean_object* v___f_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec_ref_known(v___x_1296_, 2);
v___f_1297_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152));
v___x_1298_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155);
lean_inc_ref(v_a_1173_);
v___x_1299_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1298_, v___f_1297_, v_a_1173_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1299_;
}
else
{
lean_object* v___f_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec_ref_known(v___x_1299_, 2);
v___f_1300_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156));
v___x_1301_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159);
lean_inc_ref(v_a_1173_);
v___x_1302_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1301_, v___f_1300_, v_a_1173_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_dec_ref(v_a_1173_);
return v___x_1302_;
}
else
{
lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1329_; 
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; lean_object* v_unused_1331_; 
v_unused_1330_ = lean_ctor_get(v___x_1302_, 1);
lean_dec(v_unused_1330_);
v_unused_1331_ = lean_ctor_get(v___x_1302_, 0);
lean_dec(v_unused_1331_);
v___x_1304_ = v___x_1302_;
v_isShared_1305_ = v_isSharedCheck_1329_;
goto v_resetjp_1303_;
}
else
{
lean_dec(v___x_1302_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1329_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v_snd_1310_; lean_object* v_snd_1311_; uint8_t v___x_1312_; 
v___f_1306_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1307_ = lean_unsigned_to_nat(64u);
v___x_1308_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1173_);
v___x_1309_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1306_, v___x_1307_, v___x_1308_, v_a_1173_);
v_snd_1310_ = lean_ctor_get(v___x_1309_, 1);
lean_inc(v_snd_1310_);
v_snd_1311_ = lean_ctor_get(v_snd_1310_, 1);
v___x_1312_ = lean_unbox(v_snd_1311_);
if (v___x_1312_ == 0)
{
lean_object* v_fst_1313_; lean_object* v_fst_1314_; uint8_t v___x_1315_; 
v_fst_1313_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_fst_1313_);
lean_dec_ref(v___x_1309_);
v_fst_1314_ = lean_ctor_get(v_snd_1310_, 0);
lean_inc(v_fst_1314_);
lean_dec(v_snd_1310_);
v___x_1315_ = lean_nat_dec_eq(v_fst_1313_, v___x_1308_);
lean_dec(v_fst_1313_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec_ref(v_a_1173_);
v___x_1316_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161));
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v___x_1316_);
lean_ctor_set(v___x_1304_, 0, v_fst_1314_);
v___x_1318_ = v___x_1304_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_fst_1314_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec(v_fst_1314_);
v___x_1320_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v___x_1320_);
lean_ctor_set(v___x_1304_, 0, v_a_1173_);
v___x_1322_ = v___x_1304_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_fst_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_dec_ref(v___x_1309_);
lean_dec_ref(v_a_1173_);
v_fst_1324_ = lean_ctor_get(v_snd_1310_, 0);
lean_inc(v_fst_1324_);
lean_dec(v_snd_1310_);
v___x_1325_ = lean_box(0);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v___x_1325_);
lean_ctor_set(v___x_1304_, 0, v_fst_1324_);
v___x_1327_ = v___x_1304_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_fst_1324_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
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
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1334_){
_start:
{
uint8_t v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = 32;
v___x_1336_ = lean_uint8_dec_eq(v_b_1334_, v___x_1335_);
if (v___x_1336_ == 0)
{
uint8_t v___x_1337_; 
v___x_1337_ = 1;
return v___x_1337_;
}
else
{
uint8_t v___x_1338_; 
v___x_1338_ = 0;
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1339_){
_start:
{
uint8_t v_b_boxed_1340_; uint8_t v_res_1341_; lean_object* v_r_1342_; 
v_b_boxed_1340_ = lean_unbox(v_b_1339_);
v_res_1341_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1340_);
v_r_1342_ = lean_box(v_res_1341_);
return v_r_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v_maxUriLength_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_snd_1358_; lean_object* v_snd_1359_; uint8_t v___x_1360_; 
v_maxUriLength_1354_ = lean_ctor_get(v_limits_1347_, 4);
v___f_1355_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_1356_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1348_);
v___x_1357_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1355_, v_maxUriLength_1354_, v___x_1356_, v_a_1348_);
v_snd_1358_ = lean_ctor_get(v___x_1357_, 1);
lean_inc(v_snd_1358_);
v_snd_1359_ = lean_ctor_get(v_snd_1358_, 1);
v___x_1360_ = lean_unbox(v_snd_1359_);
if (v___x_1360_ == 0)
{
lean_object* v_fst_1361_; lean_object* v_fst_1362_; lean_object* v_array_1363_; lean_object* v_idx_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1391_; 
v_fst_1361_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_fst_1361_);
lean_dec_ref(v___x_1357_);
v_fst_1362_ = lean_ctor_get(v_snd_1358_, 0);
lean_inc(v_fst_1362_);
lean_dec(v_snd_1358_);
v_array_1363_ = lean_ctor_get(v_a_1348_, 0);
v_idx_1364_ = lean_ctor_get(v_a_1348_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_a_1348_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1366_ = v_a_1348_;
v_isShared_1367_ = v_isSharedCheck_1391_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_idx_1364_);
lean_inc(v_array_1363_);
lean_dec(v_a_1348_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1391_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_lower_1369_; lean_object* v_upper_1370_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___y_1388_; uint8_t v___x_1390_; 
v___x_1385_ = lean_nat_add(v_idx_1364_, v_fst_1361_);
lean_dec(v_fst_1361_);
v___x_1386_ = lean_byte_array_size(v_array_1363_);
v___x_1390_ = lean_nat_dec_le(v_idx_1364_, v___x_1356_);
if (v___x_1390_ == 0)
{
v___y_1388_ = v_idx_1364_;
goto v___jp_1387_;
}
else
{
lean_dec(v_idx_1364_);
v___y_1388_ = v___x_1356_;
goto v___jp_1387_;
}
v___jp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1371_ = l_ByteArray_toByteSlice(v_array_1363_, v_lower_1369_, v_upper_1370_);
v___x_1372_ = l_ByteSlice_size(v___x_1371_);
v___x_1373_ = lean_nat_dec_eq(v___x_1372_, v_maxUriLength_1354_);
lean_dec(v___x_1372_);
if (v___x_1373_ == 0)
{
lean_del_object(v___x_1366_);
v___y_1350_ = v___x_1371_;
v___y_1351_ = v_fst_1362_;
goto v___jp_1349_;
}
else
{
lean_object* v_array_1374_; lean_object* v_idx_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_array_1374_ = lean_ctor_get(v_fst_1362_, 0);
v_idx_1375_ = lean_ctor_get(v_fst_1362_, 1);
v___x_1376_ = lean_byte_array_size(v_array_1374_);
v___x_1377_ = lean_nat_dec_lt(v_idx_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_del_object(v___x_1366_);
v___y_1350_ = v___x_1371_;
v___y_1351_ = v_fst_1362_;
goto v___jp_1349_;
}
else
{
uint8_t v___x_1378_; uint8_t v___x_1379_; uint8_t v___x_1380_; 
v___x_1378_ = lean_byte_array_fget(v_array_1374_, v_idx_1375_);
v___x_1379_ = 32;
v___x_1380_ = lean_uint8_dec_eq(v___x_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec_ref(v___x_1371_);
v___x_1381_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_1367_ == 0)
{
lean_ctor_set_tag(v___x_1366_, 1);
lean_ctor_set(v___x_1366_, 1, v___x_1381_);
lean_ctor_set(v___x_1366_, 0, v_fst_1362_);
v___x_1383_ = v___x_1366_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_fst_1362_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_del_object(v___x_1366_);
v___y_1350_ = v___x_1371_;
v___y_1351_ = v_fst_1362_;
goto v___jp_1349_;
}
}
}
}
v___jp_1387_:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_nat_dec_le(v___x_1385_, v___x_1386_);
if (v___x_1389_ == 0)
{
lean_dec(v___x_1385_);
v_lower_1369_ = v___y_1388_;
v_upper_1370_ = v___x_1386_;
goto v___jp_1368_;
}
else
{
v_lower_1369_ = v___y_1388_;
v_upper_1370_ = v___x_1385_;
goto v___jp_1368_;
}
}
}
}
else
{
lean_object* v_fst_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v___x_1357_);
lean_dec_ref(v_a_1348_);
v_fst_1392_ = lean_ctor_get(v_snd_1358_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_snd_1358_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v_snd_1358_, 1);
lean_dec(v_unused_1401_);
v___x_1394_ = v_snd_1358_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_fst_1392_);
lean_dec(v_snd_1358_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_box(0);
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 1);
lean_ctor_set(v___x_1394_, 1, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_fst_1392_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
v___jp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = l_ByteSlice_toByteArray(v___y_1350_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___y_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1402_, v_a_1403_);
lean_dec_ref(v_limits_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_pos_1411_; lean_object* v_array_1412_; lean_object* v_idx_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_pos_1411_ = lean_ctor_get(v___x_1410_, 0);
v_array_1412_ = lean_ctor_get(v_pos_1411_, 0);
v_idx_1413_ = lean_ctor_get(v_pos_1411_, 1);
v___x_1414_ = lean_byte_array_size(v_array_1412_);
v___x_1415_ = lean_nat_dec_lt(v_idx_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
return v___x_1410_;
}
else
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
lean_inc(v_pos_1411_);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; lean_object* v_unused_1425_; 
v_unused_1424_ = lean_ctor_get(v___x_1410_, 1);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v___x_1410_, 0);
lean_dec(v_unused_1425_);
v___x_1417_ = v___x_1410_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v___x_1410_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 1);
lean_ctor_set(v___x_1417_, 1, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_pos_1411_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
else
{
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_pos_1439_; lean_object* v_res_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1517_; 
v_pos_1439_ = lean_ctor_get(v___x_1438_, 0);
v_res_1440_ = lean_ctor_get(v___x_1438_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1442_ = v___x_1438_;
v_isShared_1443_ = v_isSharedCheck_1517_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_res_1440_);
lean_inc(v_pos_1439_);
lean_dec(v___x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1517_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_array_1444_; lean_object* v_idx_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_array_1444_ = lean_ctor_get(v_pos_1439_, 0);
v_idx_1445_ = lean_ctor_get(v_pos_1439_, 1);
v___x_1446_ = lean_byte_array_size(v_array_1444_);
v___x_1447_ = lean_nat_dec_lt(v_idx_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_dec(v_res_1440_);
v___x_1448_ = lean_box(0);
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 1);
lean_ctor_set(v___x_1442_, 1, v___x_1448_);
v___x_1450_ = v___x_1442_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_pos_1439_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
else
{
uint8_t v___x_1452_; uint8_t v_got_1453_; uint8_t v___x_1454_; 
v___x_1452_ = 32;
v_got_1453_ = lean_byte_array_fget(v_array_1444_, v_idx_1445_);
v___x_1454_ = lean_uint8_dec_eq(v_got_1453_, v___x_1452_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_dec(v_res_1440_);
v___x_1455_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 1);
lean_ctor_set(v___x_1442_, 1, v___x_1455_);
v___x_1457_ = v___x_1442_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_pos_1439_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
else
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1514_; 
lean_inc(v_idx_1445_);
lean_inc_ref(v_array_1444_);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_pos_1439_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; lean_object* v_unused_1516_; 
v_unused_1515_ = lean_ctor_get(v_pos_1439_, 1);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_pos_1439_, 0);
lean_dec(v_unused_1516_);
v___x_1460_ = v_pos_1439_;
v_isShared_1461_ = v_isSharedCheck_1514_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v_pos_1439_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1514_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_idx_1445_, v___x_1462_);
lean_dec(v_idx_1445_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_array_1444_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___f_1466_; lean_object* v___x_1467_; 
v___f_1466_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_1467_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1466_, v_res_1440_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1478_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1478_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1478_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set_tag(v___x_1470_, 1);
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 1);
lean_ctor_set(v___x_1442_, 1, v___x_1473_);
lean_ctor_set(v___x_1442_, 0, v___x_1465_);
v___x_1475_ = v___x_1442_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
lean_del_object(v___x_1442_);
v_a_1479_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1467_, 1);
v___x_1480_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v___x_1465_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_pos_1481_; lean_object* v_res_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_pos_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_pos_1481_);
v_res_1482_ = lean_ctor_get(v___x_1480_, 1);
lean_inc(v_res_1482_);
lean_dec_ref_known(v___x_1480_, 2);
v___x_1483_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_1484_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1483_, v_pos_1481_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_pos_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1493_; 
v_pos_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v___x_1484_, 1);
lean_dec(v_unused_1494_);
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_pos_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_a_1479_);
lean_ctor_set(v___x_1489_, 1, v_res_1482_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1489_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_pos_1485_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_object* v_pos_1495_; lean_object* v_err_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_res_1482_);
lean_dec(v_a_1479_);
v_pos_1495_ = lean_ctor_get(v___x_1484_, 0);
v_err_1496_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1484_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_err_1496_);
lean_inc(v_pos_1495_);
lean_dec(v___x_1484_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_pos_1495_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_err_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_pos_1504_; lean_object* v_err_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_a_1479_);
v_pos_1504_ = lean_ctor_get(v___x_1480_, 0);
v_err_1505_ = lean_ctor_get(v___x_1480_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1480_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_err_1505_);
lean_inc(v_pos_1504_);
lean_dec(v___x_1480_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_pos_1504_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_err_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
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
lean_object* v_pos_1518_; lean_object* v_err_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v_pos_1518_ = lean_ctor_get(v___x_1438_, 0);
v_err_1519_ = lean_ctor_get(v___x_1438_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1438_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_err_1519_);
lean_inc(v_pos_1518_);
lean_dec(v___x_1438_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_pos_1518_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_err_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1527_, v_a_1528_);
lean_dec_ref(v_limits_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1533_, v_a_1534_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_pos_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1626_; 
v_pos_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v___x_1535_, 1);
lean_dec(v_unused_1627_);
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1626_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_pos_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1626_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; 
v___x_1540_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1536_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_pos_1541_; lean_object* v_res_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1616_; 
v_pos_1541_ = lean_ctor_get(v___x_1540_, 0);
v_res_1542_ = lean_ctor_get(v___x_1540_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1544_ = v___x_1540_;
v_isShared_1545_ = v_isSharedCheck_1616_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_res_1542_);
lean_inc(v_pos_1541_);
lean_dec(v___x_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1616_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_array_1546_; lean_object* v_idx_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_array_1546_ = lean_ctor_get(v_pos_1541_, 0);
v_idx_1547_ = lean_ctor_get(v_pos_1541_, 1);
v___x_1548_ = lean_byte_array_size(v_array_1546_);
v___x_1549_ = lean_nat_dec_lt(v_idx_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_dec(v_res_1542_);
lean_del_object(v___x_1538_);
v___x_1550_ = lean_box(0);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 1);
lean_ctor_set(v___x_1544_, 1, v___x_1550_);
v___x_1552_ = v___x_1544_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_pos_1541_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
else
{
uint8_t v___x_1554_; uint8_t v_got_1555_; uint8_t v___x_1556_; 
v___x_1554_ = 32;
v_got_1555_ = lean_byte_array_fget(v_array_1546_, v_idx_1547_);
v___x_1556_ = lean_uint8_dec_eq(v_got_1555_, v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
lean_dec(v_res_1542_);
lean_del_object(v___x_1538_);
v___x_1557_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 1);
lean_ctor_set(v___x_1544_, 1, v___x_1557_);
v___x_1559_ = v___x_1544_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_pos_1541_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1613_; 
lean_inc(v_idx_1547_);
lean_inc_ref(v_array_1546_);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_pos_1541_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; lean_object* v_unused_1615_; 
v_unused_1614_ = lean_ctor_get(v_pos_1541_, 1);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_pos_1541_, 0);
lean_dec(v_unused_1615_);
v___x_1562_ = v_pos_1541_;
v_isShared_1563_ = v_isSharedCheck_1613_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_pos_1541_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1613_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_add(v_idx_1547_, v___x_1564_);
lean_dec(v_idx_1547_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v___x_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_array_1546_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; 
v___x_1568_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1533_, v___x_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_pos_1569_; lean_object* v_res_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1602_; 
v_pos_1569_ = lean_ctor_get(v___x_1568_, 0);
v_res_1570_ = lean_ctor_get(v___x_1568_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1572_ = v___x_1568_;
v_isShared_1573_ = v_isSharedCheck_1602_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_res_1570_);
lean_inc(v_pos_1569_);
lean_dec(v___x_1568_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1602_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_snd_1579_; lean_object* v_fst_1580_; lean_object* v_fst_1581_; lean_object* v_snd_1582_; uint8_t v___x_1583_; 
v_snd_1579_ = lean_ctor_get(v_res_1570_, 1);
lean_inc(v_snd_1579_);
v_fst_1580_ = lean_ctor_get(v_res_1570_, 0);
lean_inc(v_fst_1580_);
lean_dec(v_res_1570_);
v_fst_1581_ = lean_ctor_get(v_snd_1579_, 0);
lean_inc(v_fst_1581_);
v_snd_1582_ = lean_ctor_get(v_snd_1579_, 1);
lean_inc(v_snd_1582_);
lean_dec(v_snd_1579_);
v___x_1583_ = lean_nat_dec_eq(v_fst_1581_, v___x_1564_);
lean_dec(v_fst_1581_);
if (v___x_1583_ == 0)
{
lean_del_object(v___x_1538_);
goto v___jp_1584_;
}
else
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_nat_dec_eq(v_snd_1582_, v___x_1564_);
if (v___x_1594_ == 0)
{
lean_del_object(v___x_1538_);
goto v___jp_1584_;
}
else
{
uint8_t v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1600_; 
lean_dec(v_snd_1582_);
lean_del_object(v___x_1572_);
lean_del_object(v___x_1544_);
v___x_1595_ = 1;
v___x_1596_ = l_Std_Http_Headers_empty;
v___x_1597_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1597_, 0, v_fst_1580_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_unbox(v_res_1542_);
lean_dec(v_res_1542_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*2, v___x_1598_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*2 + 1, v___x_1595_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 1, v___x_1597_);
lean_ctor_set(v___x_1538_, 0, v_pos_1569_);
v___x_1600_ = v___x_1538_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_pos_1569_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v___x_1597_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
v___jp_1574_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 1);
lean_ctor_set(v___x_1572_, 1, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_pos_1569_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
v___jp_1584_:
{
if (v___x_1583_ == 0)
{
lean_dec(v_snd_1582_);
lean_dec(v_fst_1580_);
lean_del_object(v___x_1544_);
lean_dec(v_res_1542_);
goto v___jp_1574_;
}
else
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = lean_nat_dec_eq(v_snd_1582_, v___x_1585_);
lean_dec(v_snd_1582_);
if (v___x_1586_ == 0)
{
lean_dec(v_fst_1580_);
lean_del_object(v___x_1544_);
lean_dec(v_res_1542_);
goto v___jp_1574_;
}
else
{
uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1592_; 
lean_del_object(v___x_1572_);
v___x_1587_ = 0;
v___x_1588_ = l_Std_Http_Headers_empty;
v___x_1589_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1589_, 0, v_fst_1580_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_unbox(v_res_1542_);
lean_dec(v_res_1542_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*2, v___x_1590_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*2 + 1, v___x_1587_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v___x_1589_);
lean_ctor_set(v___x_1544_, 0, v_pos_1569_);
v___x_1592_ = v___x_1544_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_pos_1569_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1589_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1603_; lean_object* v_err_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_del_object(v___x_1544_);
lean_dec(v_res_1542_);
lean_del_object(v___x_1538_);
v_pos_1603_ = lean_ctor_get(v___x_1568_, 0);
v_err_1604_ = lean_ctor_get(v___x_1568_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1568_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_err_1604_);
lean_inc(v_pos_1603_);
lean_dec(v___x_1568_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_pos_1603_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_err_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
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
lean_object* v_pos_1617_; lean_object* v_err_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_del_object(v___x_1538_);
v_pos_1617_ = lean_ctor_get(v___x_1540_, 0);
v_err_1618_ = lean_ctor_get(v___x_1540_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1540_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_err_1618_);
lean_inc(v_pos_1617_);
lean_dec(v___x_1540_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_pos_1617_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_err_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
else
{
lean_object* v_pos_1628_; lean_object* v_err_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_pos_1628_ = lean_ctor_get(v___x_1535_, 0);
v_err_1629_ = lean_ctor_get(v___x_1535_, 1);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1535_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_err_1629_);
lean_inc(v_pos_1628_);
lean_dec(v___x_1535_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_pos_1628_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_err_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_1637_, v_a_1638_);
lean_dec_ref(v_limits_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1640_, v_a_1641_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_pos_1643_; lean_object* v___x_1644_; 
v_pos_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_pos_1643_);
lean_dec_ref_known(v___x_1642_, 2);
v___x_1644_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1643_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_pos_1645_; lean_object* v_res_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1716_; 
v_pos_1645_ = lean_ctor_get(v___x_1644_, 0);
v_res_1646_ = lean_ctor_get(v___x_1644_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1648_ = v___x_1644_;
v_isShared_1649_ = v_isSharedCheck_1716_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_res_1646_);
lean_inc(v_pos_1645_);
lean_dec(v___x_1644_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1716_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v_array_1650_; lean_object* v_idx_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_array_1650_ = lean_ctor_get(v_pos_1645_, 0);
v_idx_1651_ = lean_ctor_get(v_pos_1645_, 1);
v___x_1652_ = lean_byte_array_size(v_array_1650_);
v___x_1653_ = lean_nat_dec_lt(v_idx_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
lean_dec(v_res_1646_);
v___x_1654_ = lean_box(0);
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 1);
lean_ctor_set(v___x_1648_, 1, v___x_1654_);
v___x_1656_ = v___x_1648_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_pos_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
else
{
uint8_t v___x_1658_; uint8_t v_got_1659_; uint8_t v___x_1660_; 
v___x_1658_ = 32;
v_got_1659_ = lean_byte_array_fget(v_array_1650_, v_idx_1651_);
v___x_1660_ = lean_uint8_dec_eq(v_got_1659_, v___x_1658_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_res_1646_);
v___x_1661_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 1);
lean_ctor_set(v___x_1648_, 1, v___x_1661_);
v___x_1663_ = v___x_1648_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_pos_1645_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
else
{
lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1713_; 
lean_inc(v_idx_1651_);
lean_inc_ref(v_array_1650_);
lean_del_object(v___x_1648_);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_pos_1645_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; lean_object* v_unused_1715_; 
v_unused_1714_ = lean_ctor_get(v_pos_1645_, 1);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v_pos_1645_, 0);
lean_dec(v_unused_1715_);
v___x_1666_ = v_pos_1645_;
v_isShared_1667_ = v_isSharedCheck_1713_;
goto v_resetjp_1665_;
}
else
{
lean_dec(v_pos_1645_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1713_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_nat_add(v_idx_1651_, v___x_1668_);
lean_dec(v_idx_1651_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1669_);
v___x_1671_ = v___x_1666_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_array_1650_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1640_, v___x_1671_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_res_1673_; lean_object* v_snd_1674_; lean_object* v_pos_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1701_; 
v_res_1673_ = lean_ctor_get(v___x_1672_, 1);
lean_inc(v_res_1673_);
v_snd_1674_ = lean_ctor_get(v_res_1673_, 1);
lean_inc(v_snd_1674_);
v_pos_1675_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___x_1672_, 1);
lean_dec(v_unused_1702_);
v___x_1677_ = v___x_1672_;
v_isShared_1678_ = v_isSharedCheck_1701_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_pos_1675_);
lean_dec(v___x_1672_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1701_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_fst_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1699_; 
v_fst_1679_ = lean_ctor_get(v_res_1673_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_res_1673_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v_res_1673_, 1);
lean_dec(v_unused_1700_);
v___x_1681_ = v_res_1673_;
v_isShared_1682_ = v_isSharedCheck_1699_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_fst_1679_);
lean_dec(v_res_1673_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1699_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_fst_1683_; lean_object* v_snd_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1698_; 
v_fst_1683_ = lean_ctor_get(v_snd_1674_, 0);
v_snd_1684_ = lean_ctor_get(v_snd_1674_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_snd_1674_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1686_ = v_snd_1674_;
v_isShared_1687_ = v_isSharedCheck_1698_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snd_1684_);
lean_inc(v_fst_1683_);
lean_dec(v_snd_1674_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1698_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = l_Std_Http_Version_ofNumber_x3f(v_fst_1683_, v_snd_1684_);
lean_dec(v_snd_1684_);
lean_dec(v_fst_1683_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1688_);
lean_ctor_set(v___x_1686_, 0, v_fst_1679_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_fst_1679_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1692_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1690_);
lean_ctor_set(v___x_1681_, 0, v_res_1646_);
v___x_1692_ = v___x_1681_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_res_1646_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1694_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v___x_1692_);
v___x_1694_ = v___x_1677_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_pos_1675_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_1703_; lean_object* v_err_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_res_1646_);
v_pos_1703_ = lean_ctor_get(v___x_1672_, 0);
v_err_1704_ = lean_ctor_get(v___x_1672_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1672_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_err_1704_);
lean_inc(v_pos_1703_);
lean_dec(v___x_1672_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_pos_1703_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_err_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
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
lean_object* v_pos_1717_; lean_object* v_err_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_pos_1717_ = lean_ctor_get(v___x_1644_, 0);
v_err_1718_ = lean_ctor_get(v___x_1644_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1644_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_err_1718_);
lean_inc(v_pos_1717_);
lean_dec(v___x_1644_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_pos_1717_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_err_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_pos_1726_; lean_object* v_err_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_pos_1726_ = lean_ctor_get(v___x_1642_, 0);
v_err_1727_ = lean_ctor_get(v___x_1642_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1642_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_err_1727_);
lean_inc(v_pos_1726_);
lean_dec(v___x_1642_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_pos_1726_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_err_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_1735_, v_a_1736_);
lean_dec_ref(v_limits_1735_);
return v_res_1737_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_1738_){
_start:
{
uint32_t v___x_1739_; uint32_t v___x_1740_; uint8_t v___x_1741_; 
v___x_1739_ = lean_uint8_to_uint32(v___y_1738_);
v___x_1740_ = 32;
v___x_1741_ = lean_uint32_dec_eq(v___x_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
uint32_t v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = 9;
v___x_1743_ = lean_uint32_dec_eq(v___x_1739_, v___x_1742_);
return v___x_1743_;
}
else
{
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_1744_){
_start:
{
uint8_t v___y_3721__boxed_1745_; uint8_t v_res_1746_; lean_object* v_r_1747_; 
v___y_3721__boxed_1745_ = lean_unbox(v___y_1744_);
v_res_1746_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_3721__boxed_1745_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(uint8_t v___y_1748_){
_start:
{
uint32_t v___x_1749_; uint32_t v___x_1755_; uint8_t v___x_1756_; 
v___x_1749_ = lean_uint8_to_uint32(v___y_1748_);
v___x_1755_ = 33;
v___x_1756_ = lean_uint32_dec_le(v___x_1755_, v___x_1749_);
if (v___x_1756_ == 0)
{
goto v___jp_1750_;
}
else
{
uint32_t v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = 126;
v___x_1758_ = lean_uint32_dec_le(v___x_1749_, v___x_1757_);
if (v___x_1758_ == 0)
{
goto v___jp_1750_;
}
else
{
return v___x_1758_;
}
}
v___jp_1750_:
{
uint32_t v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = 32;
v___x_1752_ = lean_uint32_dec_eq(v___x_1749_, v___x_1751_);
if (v___x_1752_ == 0)
{
uint32_t v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = 9;
v___x_1754_ = lean_uint32_dec_eq(v___x_1749_, v___x_1753_);
return v___x_1754_;
}
else
{
return v___x_1752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed(lean_object* v___y_1759_){
_start:
{
uint8_t v___y_3734__boxed_1760_; uint8_t v_res_1761_; lean_object* v_r_1762_; 
v___y_3734__boxed_1760_ = lean_unbox(v___y_1759_);
v_res_1761_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(v___y_3734__boxed_1760_);
v_r_1762_ = lean_box(v_res_1761_);
return v_r_1762_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_1763_, lean_object* v_pos_1764_){
_start:
{
lean_object* v_str_1765_; lean_object* v_startInclusive_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v_decide_1770_; 
v_str_1765_ = lean_ctor_get(v_s_1763_, 0);
v_startInclusive_1766_ = lean_ctor_get(v_s_1763_, 1);
v___x_1767_ = lean_nat_add(v_startInclusive_1766_, v_pos_1764_);
v___x_1768_ = lean_nat_sub(v___x_1767_, v_startInclusive_1766_);
v___x_1769_ = lean_unsigned_to_nat(0u);
v_decide_1770_ = lean_nat_dec_eq(v___x_1768_, v___x_1769_);
if (v_decide_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1779_; uint32_t v___x_1780_; uint32_t v___x_1781_; uint8_t v___x_1782_; 
lean_inc(v_startInclusive_1766_);
lean_inc_ref(v_str_1765_);
v___x_1771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1771_, 0, v_str_1765_);
lean_ctor_set(v___x_1771_, 1, v_startInclusive_1766_);
lean_ctor_set(v___x_1771_, 2, v___x_1767_);
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_nat_sub(v___x_1768_, v___x_1772_);
lean_dec(v___x_1768_);
v___x_1774_ = l_String_Slice_posLE(v___x_1771_, v___x_1773_);
lean_dec_ref_known(v___x_1771_, 3);
v___x_1779_ = lean_nat_add(v_startInclusive_1766_, v___x_1774_);
v___x_1780_ = lean_string_utf8_get_fast(v_str_1765_, v___x_1779_);
lean_dec(v___x_1779_);
v___x_1781_ = 32;
v___x_1782_ = lean_uint32_dec_eq(v___x_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
uint32_t v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = 9;
v___x_1784_ = lean_uint32_dec_eq(v___x_1780_, v___x_1783_);
if (v___x_1784_ == 0)
{
uint32_t v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = 13;
v___x_1786_ = lean_uint32_dec_eq(v___x_1780_, v___x_1785_);
if (v___x_1786_ == 0)
{
uint32_t v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = 10;
v___x_1788_ = lean_uint32_dec_eq(v___x_1780_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_dec(v___x_1774_);
return v_pos_1764_;
}
else
{
goto v___jp_1775_;
}
}
else
{
goto v___jp_1775_;
}
}
else
{
goto v___jp_1775_;
}
}
else
{
goto v___jp_1775_;
}
v___jp_1775_:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_nat_add(v___x_1774_, v___x_1772_);
v___x_1777_ = lean_nat_dec_le(v___x_1776_, v_pos_1764_);
lean_dec(v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec(v___x_1774_);
return v_pos_1764_;
}
else
{
lean_dec(v_pos_1764_);
v_pos_1764_ = v___x_1774_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1768_);
lean_dec(v___x_1767_);
return v_pos_1764_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_1789_, lean_object* v_pos_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_1789_, v_pos_1790_);
lean_dec_ref(v_s_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_pos_1800_; lean_object* v_pos_1804_; lean_object* v_maxHeaderNameLength_1807_; lean_object* v_maxHeaderValueLength_1808_; lean_object* v_maxSpaceSequence_1809_; lean_object* v___f_1810_; lean_object* v___x_1811_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1871_; lean_object* v_pos_1872_; lean_object* v_res_1873_; lean_object* v___x_1879_; lean_object* v_snd_1880_; lean_object* v_snd_1881_; uint8_t v___x_1882_; 
v_maxHeaderNameLength_1807_ = lean_ctor_get(v_limits_1797_, 6);
v_maxHeaderValueLength_1808_ = lean_ctor_get(v_limits_1797_, 7);
v_maxSpaceSequence_1809_ = lean_ctor_get(v_limits_1797_, 8);
v___f_1810_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1811_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1798_);
v___x_1879_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1810_, v_maxHeaderNameLength_1807_, v___x_1811_, v_a_1798_);
v_snd_1880_ = lean_ctor_get(v___x_1879_, 1);
lean_inc(v_snd_1880_);
v_snd_1881_ = lean_ctor_get(v_snd_1880_, 1);
v___x_1882_ = lean_unbox(v_snd_1881_);
if (v___x_1882_ == 0)
{
lean_object* v_fst_1883_; lean_object* v_fst_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_2042_; 
v_fst_1883_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_fst_1883_);
lean_dec_ref(v___x_1879_);
v_fst_1884_ = lean_ctor_get(v_snd_1880_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_snd_1880_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v_snd_1880_, 1);
lean_dec(v_unused_2043_);
v___x_1886_ = v_snd_1880_;
v_isShared_1887_ = v_isSharedCheck_2042_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_fst_1884_);
lean_dec(v_snd_1880_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_2042_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_eq(v_fst_1883_, v___x_1811_);
if (v___x_1888_ == 0)
{
lean_object* v_array_1889_; lean_object* v_idx_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_2037_; 
v_array_1889_ = lean_ctor_get(v_a_1798_, 0);
v_idx_1890_ = lean_ctor_get(v_a_1798_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_1798_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_1892_ = v_a_1798_;
v_isShared_1893_ = v_isSharedCheck_2037_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_idx_1890_);
lean_inc(v_array_1889_);
lean_dec(v_a_1798_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_2037_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___f_1894_; lean_object* v___y_1896_; lean_object* v_pos_1897_; lean_object* v_res_1898_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v_lower_1928_; lean_object* v_upper_1929_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___f_1940_; lean_object* v___y_1942_; lean_object* v_pos_1943_; lean_object* v___y_1970_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___y_2028_; uint8_t v___x_2036_; 
v___f_1894_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___f_1940_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_2025_ = lean_nat_add(v_idx_1890_, v_fst_1883_);
lean_dec(v_fst_1883_);
v___x_2026_ = lean_byte_array_size(v_array_1889_);
v___x_2036_ = lean_nat_dec_le(v_idx_1890_, v___x_1811_);
if (v___x_2036_ == 0)
{
v___y_2028_ = v_idx_1890_;
goto v___jp_2027_;
}
else
{
lean_dec(v_idx_1890_);
v___y_2028_ = v___x_1811_;
goto v___jp_2027_;
}
v___jp_1895_:
{
lean_object* v___x_1899_; lean_object* v_snd_1900_; lean_object* v_snd_1901_; uint8_t v___x_1902_; 
v___x_1899_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1894_, v_maxSpaceSequence_1809_, v___x_1811_, v_pos_1897_);
v_snd_1900_ = lean_ctor_get(v___x_1899_, 1);
lean_inc(v_snd_1900_);
lean_dec_ref(v___x_1899_);
v_snd_1901_ = lean_ctor_get(v_snd_1900_, 1);
v___x_1902_ = lean_unbox(v_snd_1901_);
if (v___x_1902_ == 0)
{
lean_object* v_fst_1903_; lean_object* v_array_1904_; lean_object* v_idx_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_fst_1903_ = lean_ctor_get(v_snd_1900_, 0);
lean_inc(v_fst_1903_);
lean_dec(v_snd_1900_);
v_array_1904_ = lean_ctor_get(v_fst_1903_, 0);
v_idx_1905_ = lean_ctor_get(v_fst_1903_, 1);
v___x_1906_ = lean_byte_array_size(v_array_1904_);
v___x_1907_ = lean_nat_dec_lt(v_idx_1905_, v___x_1906_);
if (v___x_1907_ == 0)
{
v___y_1871_ = v___y_1896_;
v_pos_1872_ = v_fst_1903_;
v_res_1873_ = v_res_1898_;
goto v___jp_1870_;
}
else
{
uint8_t v___x_1908_; uint32_t v___x_1909_; uint32_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1908_ = lean_byte_array_fget(v_array_1904_, v_idx_1905_);
v___x_1909_ = lean_uint8_to_uint32(v___x_1908_);
v___x_1910_ = 32;
v___x_1911_ = lean_uint32_dec_eq(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
uint32_t v___x_1912_; uint8_t v___x_1913_; 
v___x_1912_ = 9;
v___x_1913_ = lean_uint32_dec_eq(v___x_1909_, v___x_1912_);
if (v___x_1913_ == 0)
{
v___y_1871_ = v___y_1896_;
v_pos_1872_ = v_fst_1903_;
v_res_1873_ = v_res_1898_;
goto v___jp_1870_;
}
else
{
lean_dec(v_res_1898_);
lean_dec_ref(v___y_1896_);
v_pos_1804_ = v_fst_1903_;
goto v___jp_1803_;
}
}
else
{
lean_dec(v_res_1898_);
lean_dec_ref(v___y_1896_);
v_pos_1804_ = v_fst_1903_;
goto v___jp_1803_;
}
}
}
else
{
lean_object* v_fst_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_res_1898_);
lean_dec_ref(v___y_1896_);
v_fst_1914_ = lean_ctor_get(v_snd_1900_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_snd_1900_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v_snd_1900_, 1);
lean_dec(v_unused_1923_);
v___x_1916_ = v_snd_1900_;
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_fst_1914_);
lean_dec(v_snd_1900_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_box(0);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
lean_ctor_set(v___x_1916_, 1, v___x_1918_);
v___x_1920_ = v___x_1916_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_fst_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
v___jp_1924_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = l_ByteArray_toByteSlice(v___y_1925_, v_lower_1928_, v_upper_1929_);
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
v___y_1896_ = v___y_1927_;
v_pos_1897_ = v___y_1926_;
v_res_1898_ = v___x_1931_;
goto v___jp_1895_;
}
v___jp_1932_:
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_nat_dec_le(v___y_1934_, v___y_1937_);
if (v___x_1939_ == 0)
{
lean_dec(v___y_1934_);
v___y_1925_ = v___y_1933_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___y_1936_;
v_lower_1928_ = v___y_1938_;
v_upper_1929_ = v___y_1937_;
goto v___jp_1924_;
}
else
{
lean_dec(v___y_1937_);
v___y_1925_ = v___y_1933_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___y_1936_;
v_lower_1928_ = v___y_1938_;
v_upper_1929_ = v___y_1934_;
goto v___jp_1924_;
}
}
v___jp_1941_:
{
lean_object* v___x_1944_; lean_object* v_snd_1945_; lean_object* v_snd_1946_; uint8_t v___x_1947_; 
lean_inc_ref(v_pos_1943_);
v___x_1944_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1940_, v_maxHeaderValueLength_1808_, v___x_1811_, v_pos_1943_);
v_snd_1945_ = lean_ctor_get(v___x_1944_, 1);
lean_inc(v_snd_1945_);
v_snd_1946_ = lean_ctor_get(v_snd_1945_, 1);
v___x_1947_ = lean_unbox(v_snd_1946_);
if (v___x_1947_ == 0)
{
lean_object* v_fst_1948_; lean_object* v_fst_1949_; lean_object* v_array_1950_; lean_object* v_idx_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_fst_1948_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_fst_1948_);
lean_dec_ref(v___x_1944_);
v_fst_1949_ = lean_ctor_get(v_snd_1945_, 0);
lean_inc(v_fst_1949_);
lean_dec(v_snd_1945_);
v_array_1950_ = lean_ctor_get(v_pos_1943_, 0);
lean_inc_ref(v_array_1950_);
v_idx_1951_ = lean_ctor_get(v_pos_1943_, 1);
lean_inc(v_idx_1951_);
lean_dec_ref(v_pos_1943_);
v___x_1952_ = lean_nat_add(v_idx_1951_, v_fst_1948_);
lean_dec(v_fst_1948_);
v___x_1953_ = lean_byte_array_size(v_array_1950_);
v___x_1954_ = lean_nat_dec_le(v_idx_1951_, v___x_1811_);
if (v___x_1954_ == 0)
{
v___y_1933_ = v_array_1950_;
v___y_1934_ = v___x_1952_;
v___y_1935_ = v_fst_1949_;
v___y_1936_ = v___y_1942_;
v___y_1937_ = v___x_1953_;
v___y_1938_ = v_idx_1951_;
goto v___jp_1932_;
}
else
{
lean_dec(v_idx_1951_);
v___y_1933_ = v_array_1950_;
v___y_1934_ = v___x_1952_;
v___y_1935_ = v_fst_1949_;
v___y_1936_ = v___y_1942_;
v___y_1937_ = v___x_1953_;
v___y_1938_ = v___x_1811_;
goto v___jp_1932_;
}
}
else
{
lean_object* v_fst_1955_; lean_object* v_idx_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v___x_1944_);
v_fst_1955_ = lean_ctor_get(v_snd_1945_, 0);
lean_inc(v_fst_1955_);
lean_dec(v_snd_1945_);
v_idx_1956_ = lean_ctor_get(v_pos_1943_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_pos_1943_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v_pos_1943_, 0);
lean_dec(v_unused_1968_);
v___x_1958_ = v_pos_1943_;
v_isShared_1959_ = v_isSharedCheck_1967_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_idx_1956_);
lean_dec(v_pos_1943_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1967_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_idx_1960_; uint8_t v___x_1961_; 
v_idx_1960_ = lean_ctor_get(v_fst_1955_, 1);
v___x_1961_ = lean_nat_dec_eq(v_idx_1956_, v_idx_1960_);
lean_dec(v_idx_1956_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec_ref(v___y_1942_);
v___x_1962_ = lean_box(0);
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 1);
lean_ctor_set(v___x_1958_, 1, v___x_1962_);
lean_ctor_set(v___x_1958_, 0, v_fst_1955_);
v___x_1964_ = v___x_1958_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_fst_1955_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
lean_object* v___x_1966_; 
lean_del_object(v___x_1958_);
v___x_1966_ = lean_box(0);
v___y_1896_ = v___y_1942_;
v_pos_1897_ = v_fst_1955_;
v_res_1898_ = v___x_1966_;
goto v___jp_1895_;
}
}
}
}
v___jp_1969_:
{
lean_object* v_array_1971_; lean_object* v_idx_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v_array_1971_ = lean_ctor_get(v_fst_1884_, 0);
v_idx_1972_ = lean_ctor_get(v_fst_1884_, 1);
v___x_1973_ = lean_byte_array_size(v_array_1971_);
v___x_1974_ = lean_nat_dec_lt(v_idx_1972_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec_ref(v___y_1970_);
lean_dec_ref(v_array_1889_);
v___x_1975_ = lean_box(0);
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 1);
lean_ctor_set(v___x_1892_, 1, v___x_1975_);
lean_ctor_set(v___x_1892_, 0, v_fst_1884_);
v___x_1977_ = v___x_1892_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_fst_1884_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
else
{
uint8_t v___x_1979_; uint8_t v_got_1980_; uint8_t v___x_1981_; 
v___x_1979_ = 58;
v_got_1980_ = lean_byte_array_fget(v_array_1971_, v_idx_1972_);
v___x_1981_ = lean_uint8_dec_eq(v_got_1980_, v___x_1979_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
lean_dec_ref(v___y_1970_);
lean_dec_ref(v_array_1889_);
v___x_1982_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 1);
lean_ctor_set(v___x_1892_, 1, v___x_1982_);
lean_ctor_set(v___x_1892_, 0, v_fst_1884_);
v___x_1984_ = v___x_1892_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_fst_1884_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
else
{
lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2022_; 
lean_inc(v_idx_1972_);
lean_inc_ref(v_array_1971_);
lean_del_object(v___x_1892_);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_fst_1884_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; lean_object* v_unused_2024_; 
v_unused_2023_ = lean_ctor_get(v_fst_1884_, 1);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_fst_1884_, 0);
lean_dec(v_unused_2024_);
v___x_1987_ = v_fst_1884_;
v_isShared_1988_ = v_isSharedCheck_2022_;
goto v_resetjp_1986_;
}
else
{
lean_dec(v_fst_1884_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2022_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = lean_nat_add(v_idx_1972_, v___x_1989_);
lean_dec(v_idx_1972_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v___x_1990_);
v___x_1992_ = v___x_1987_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_array_1971_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_2021_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v_snd_1994_; lean_object* v_snd_1995_; uint8_t v___x_1996_; 
v___x_1993_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1894_, v_maxSpaceSequence_1809_, v___x_1811_, v___x_1992_);
v_snd_1994_ = lean_ctor_get(v___x_1993_, 1);
lean_inc(v_snd_1994_);
lean_dec_ref(v___x_1993_);
v_snd_1995_ = lean_ctor_get(v_snd_1994_, 1);
v___x_1996_ = lean_unbox(v_snd_1995_);
if (v___x_1996_ == 0)
{
lean_object* v_fst_1997_; lean_object* v_array_1998_; lean_object* v_idx_1999_; lean_object* v_lower_2000_; lean_object* v_upper_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v_fst_1997_ = lean_ctor_get(v_snd_1994_, 0);
lean_inc(v_fst_1997_);
lean_dec(v_snd_1994_);
v_array_1998_ = lean_ctor_get(v_fst_1997_, 0);
v_idx_1999_ = lean_ctor_get(v_fst_1997_, 1);
v_lower_2000_ = lean_ctor_get(v___y_1970_, 0);
lean_inc(v_lower_2000_);
v_upper_2001_ = lean_ctor_get(v___y_1970_, 1);
lean_inc(v_upper_2001_);
lean_dec_ref(v___y_1970_);
v___x_2002_ = l_ByteArray_toByteSlice(v_array_1889_, v_lower_2000_, v_upper_2001_);
v___x_2003_ = lean_byte_array_size(v_array_1998_);
v___x_2004_ = lean_nat_dec_lt(v_idx_1999_, v___x_2003_);
if (v___x_2004_ == 0)
{
v___y_1942_ = v___x_2002_;
v_pos_1943_ = v_fst_1997_;
goto v___jp_1941_;
}
else
{
uint8_t v___x_2005_; uint32_t v___x_2006_; uint32_t v___x_2007_; uint8_t v___x_2008_; 
v___x_2005_ = lean_byte_array_fget(v_array_1998_, v_idx_1999_);
v___x_2006_ = lean_uint8_to_uint32(v___x_2005_);
v___x_2007_ = 32;
v___x_2008_ = lean_uint32_dec_eq(v___x_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
uint32_t v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = 9;
v___x_2010_ = lean_uint32_dec_eq(v___x_2006_, v___x_2009_);
if (v___x_2010_ == 0)
{
v___y_1942_ = v___x_2002_;
v_pos_1943_ = v_fst_1997_;
goto v___jp_1941_;
}
else
{
lean_dec_ref(v___x_2002_);
v_pos_1800_ = v_fst_1997_;
goto v___jp_1799_;
}
}
else
{
lean_dec_ref(v___x_2002_);
v_pos_1800_ = v_fst_1997_;
goto v___jp_1799_;
}
}
}
else
{
lean_object* v_fst_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v___y_1970_);
lean_dec_ref(v_array_1889_);
v_fst_2011_ = lean_ctor_get(v_snd_1994_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_snd_1994_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v_snd_1994_, 1);
lean_dec(v_unused_2020_);
v___x_2013_ = v_snd_1994_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_fst_2011_);
lean_dec(v_snd_1994_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_box(0);
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 1);
lean_ctor_set(v___x_2013_, 1, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_fst_2011_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
}
}
}
v___jp_2027_:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_nat_dec_le(v___x_2025_, v___x_2026_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2031_; 
lean_dec(v___x_2025_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v___x_2026_);
lean_ctor_set(v___x_1886_, 0, v___y_2028_);
v___x_2031_ = v___x_1886_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___y_2028_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
v___y_1970_ = v___x_2031_;
goto v___jp_1969_;
}
}
else
{
lean_object* v___x_2034_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v___x_2025_);
lean_ctor_set(v___x_1886_, 0, v___y_2028_);
v___x_2034_ = v___x_1886_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___y_2028_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2025_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
v___y_1970_ = v___x_2034_;
goto v___jp_1969_;
}
}
}
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_dec(v_fst_1884_);
lean_dec(v_fst_1883_);
v___x_2038_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 1);
lean_ctor_set(v___x_1886_, 1, v___x_2038_);
lean_ctor_set(v___x_1886_, 0, v_a_1798_);
v___x_2040_ = v___x_1886_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_1798_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_fst_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v___x_1879_);
lean_dec_ref(v_a_1798_);
v_fst_2044_ = lean_ctor_get(v_snd_1880_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_snd_1880_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v_snd_1880_, 1);
lean_dec(v_unused_2053_);
v___x_2046_ = v_snd_1880_;
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_fst_2044_);
lean_dec(v_snd_1880_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_box(0);
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 1);
lean_ctor_set(v___x_2046_, 1, v___x_2048_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_fst_2044_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
v___jp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v_pos_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
return v___x_1802_;
}
v___jp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1806_, 0, v_pos_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
return v___x_1806_;
}
v___jp_1812_:
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_1815_, v___y_1813_);
lean_dec(v___y_1815_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_pos_1817_; lean_object* v_res_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1831_; 
v_pos_1817_ = lean_ctor_get(v___x_1816_, 0);
v_res_1818_ = lean_ctor_get(v___x_1816_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1820_ = v___x_1816_;
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_res_1818_);
lean_inc(v_pos_1817_);
lean_dec(v___x_1816_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1831_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1822_ = lean_string_utf8_byte_size(v_res_1818_);
lean_inc(v_res_1818_);
v___x_1823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1823_, 0, v_res_1818_);
lean_ctor_set(v___x_1823_, 1, v___x_1811_);
lean_ctor_set(v___x_1823_, 2, v___x_1822_);
v___x_1824_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_1823_, v___x_1822_);
lean_dec_ref_known(v___x_1823_, 3);
v___x_1825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1825_, 0, v_res_1818_);
lean_ctor_set(v___x_1825_, 1, v___x_1811_);
lean_ctor_set(v___x_1825_, 2, v___x_1824_);
v___x_1826_ = l_String_Slice_toString(v___x_1825_);
lean_dec_ref_known(v___x_1825_, 3);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___y_1814_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___x_1827_);
v___x_1829_ = v___x_1820_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_pos_1817_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
lean_object* v_pos_1832_; lean_object* v_err_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v___y_1814_);
v_pos_1832_ = lean_ctor_get(v___x_1816_, 0);
v_err_1833_ = lean_ctor_get(v___x_1816_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1816_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_err_1833_);
lean_inc(v_pos_1832_);
lean_dec(v___x_1816_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_pos_1832_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_err_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
v___jp_1841_:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_string_validate_utf8(v___y_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref(v___y_1844_);
v___x_1846_ = lean_box(0);
v___y_1813_ = v___y_1842_;
v___y_1814_ = v___y_1843_;
v___y_1815_ = v___x_1846_;
goto v___jp_1812_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_string_from_utf8_unchecked(v___y_1844_);
v___x_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
v___y_1813_ = v___y_1842_;
v___y_1814_ = v___y_1843_;
v___y_1815_ = v___x_1848_;
goto v___jp_1812_;
}
}
v___jp_1849_:
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_1852_, v___y_1851_);
lean_dec(v___y_1852_);
if (lean_obj_tag(v___x_1853_) == 0)
{
if (lean_obj_tag(v___y_1850_) == 0)
{
lean_object* v_pos_1854_; lean_object* v_res_1855_; lean_object* v___x_1856_; 
v_pos_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_pos_1854_);
v_res_1855_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_res_1855_);
lean_dec_ref_known(v___x_1853_, 2);
v___x_1856_ = l_ByteArray_empty;
v___y_1842_ = v_pos_1854_;
v___y_1843_ = v_res_1855_;
v___y_1844_ = v___x_1856_;
goto v___jp_1841_;
}
else
{
lean_object* v_pos_1857_; lean_object* v_res_1858_; lean_object* v_val_1859_; lean_object* v___x_1860_; 
v_pos_1857_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_pos_1857_);
v_res_1858_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_res_1858_);
lean_dec_ref_known(v___x_1853_, 2);
v_val_1859_ = lean_ctor_get(v___y_1850_, 0);
lean_inc(v_val_1859_);
lean_dec_ref_known(v___y_1850_, 1);
v___x_1860_ = l_ByteSlice_toByteArray(v_val_1859_);
v___y_1842_ = v_pos_1857_;
v___y_1843_ = v_res_1858_;
v___y_1844_ = v___x_1860_;
goto v___jp_1841_;
}
}
else
{
lean_object* v_pos_1861_; lean_object* v_err_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v___y_1850_);
v_pos_1861_ = lean_ctor_get(v___x_1853_, 0);
v_err_1862_ = lean_ctor_get(v___x_1853_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1853_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_err_1862_);
lean_inc(v_pos_1861_);
lean_dec(v___x_1853_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_pos_1861_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_err_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
v___jp_1870_:
{
lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___x_1874_ = l_ByteSlice_toByteArray(v___y_1871_);
v___x_1875_ = lean_string_validate_utf8(v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; 
lean_dec_ref(v___x_1874_);
v___x_1876_ = lean_box(0);
v___y_1850_ = v_res_1873_;
v___y_1851_ = v_pos_1872_;
v___y_1852_ = v___x_1876_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_string_from_utf8_unchecked(v___x_1874_);
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___y_1850_ = v_res_1873_;
v___y_1851_ = v_pos_1872_;
v___y_1852_ = v___x_1878_;
goto v___jp_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2054_, v_a_2055_);
lean_dec_ref(v_limits_2054_);
return v_res_2056_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
if (lean_obj_tag(v_x_2057_) == 0)
{
if (lean_obj_tag(v_x_2058_) == 0)
{
uint8_t v___x_2059_; 
v___x_2059_ = 1;
return v___x_2059_;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = 0;
return v___x_2060_;
}
}
else
{
if (lean_obj_tag(v_x_2058_) == 0)
{
uint8_t v___x_2061_; 
v___x_2061_ = 0;
return v___x_2061_;
}
else
{
lean_object* v_val_2062_; lean_object* v_val_2063_; uint8_t v___x_2064_; uint8_t v___x_2065_; uint8_t v___x_2066_; 
v_val_2062_ = lean_ctor_get(v_x_2057_, 0);
v_val_2063_ = lean_ctor_get(v_x_2058_, 0);
v___x_2064_ = lean_unbox(v_val_2062_);
v___x_2065_ = lean_unbox(v_val_2063_);
v___x_2066_ = lean_uint8_dec_eq(v___x_2064_, v___x_2065_);
return v___x_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
uint8_t v_res_2069_; lean_object* v_r_2070_; 
v_res_2069_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2067_, v_x_2068_);
lean_dec(v_x_2068_);
lean_dec(v_x_2067_);
v_r_2070_ = lean_box(v_res_2069_);
return v_r_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___y_2080_; lean_object* v_pos_2103_; lean_object* v_res_2104_; lean_object* v_array_2142_; lean_object* v_idx_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v_array_2142_ = lean_ctor_get(v_a_2078_, 0);
v_idx_2143_ = lean_ctor_get(v_a_2078_, 1);
v___x_2144_ = lean_byte_array_size(v_array_2142_);
v___x_2145_ = lean_nat_dec_lt(v_idx_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_box(0);
v_pos_2103_ = v_a_2078_;
v_res_2104_ = v___x_2146_;
goto v___jp_2102_;
}
else
{
uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = lean_byte_array_fget(v_array_2142_, v_idx_2143_);
v___x_2148_ = lean_box(v___x_2147_);
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
v_pos_2103_ = v_a_2078_;
v_res_2104_ = v___x_2149_;
goto v___jp_2102_;
}
v___jp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2082_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2081_, v___y_2080_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_pos_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2091_; 
v_pos_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v___x_2082_, 1);
lean_dec(v_unused_2092_);
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_pos_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_box(0);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 1, v___x_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_pos_2083_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
else
{
lean_object* v_pos_2093_; lean_object* v_err_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
v_pos_2093_ = lean_ctor_get(v___x_2082_, 0);
v_err_2094_ = lean_ctor_get(v___x_2082_, 1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2082_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_err_2094_);
lean_inc(v_pos_2093_);
lean_dec(v___x_2082_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_pos_2093_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_err_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
v___jp_2102_:
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_2106_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_2108_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2104_, v___x_2107_);
lean_dec(v_res_2104_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2077_, v_pos_2103_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_pos_2110_; lean_object* v_res_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_pos_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_pos_2110_);
v_res_2111_ = lean_ctor_get(v___x_2109_, 1);
lean_inc(v_res_2111_);
lean_dec_ref_known(v___x_2109_, 2);
v___x_2112_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2113_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2112_, v_pos_2110_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_pos_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2122_; 
v_pos_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v___x_2113_, 1);
lean_dec(v_unused_2123_);
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_pos_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_res_2111_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 1, v___x_2118_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_pos_2114_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_pos_2124_; lean_object* v_err_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_res_2111_);
v_pos_2124_ = lean_ctor_get(v___x_2113_, 0);
v_err_2125_ = lean_ctor_get(v___x_2113_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2113_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_err_2125_);
lean_inc(v_pos_2124_);
lean_dec(v___x_2113_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_pos_2124_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_err_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_pos_2133_; lean_object* v_err_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_pos_2133_ = lean_ctor_get(v___x_2109_, 0);
v_err_2134_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2109_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_err_2134_);
lean_inc(v_pos_2133_);
lean_dec(v___x_2109_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_pos_2133_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_err_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
v___y_2080_ = v_pos_2103_;
goto v___jp_2079_;
}
}
else
{
lean_dec(v_res_2104_);
v___y_2080_ = v_pos_2103_;
goto v___jp_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2150_, v_a_2151_);
lean_dec_ref(v_limits_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2157_){
_start:
{
lean_object* v_array_2158_; lean_object* v_idx_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v_array_2158_ = lean_ctor_get(v_a_2157_, 0);
v_idx_2159_ = lean_ctor_get(v_a_2157_, 1);
v___x_2160_ = lean_byte_array_size(v_array_2158_);
v___x_2161_ = lean_nat_dec_lt(v_idx_2159_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_box(0);
v___x_2163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2163_, 0, v_a_2157_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
return v___x_2163_;
}
else
{
uint8_t v___x_2164_; uint8_t v_got_2165_; uint8_t v___x_2166_; 
v___x_2164_ = 92;
v_got_2165_ = lean_byte_array_fget(v_array_2158_, v_idx_2159_);
v___x_2166_ = lean_uint8_dec_eq(v_got_2165_, v___x_2164_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_a_2157_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
return v___x_2168_;
}
else
{
lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2202_; 
lean_inc(v_idx_2159_);
lean_inc_ref(v_array_2158_);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_a_2157_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; lean_object* v_unused_2204_; 
v_unused_2203_ = lean_ctor_get(v_a_2157_, 1);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_a_2157_, 0);
lean_dec(v_unused_2204_);
v___x_2170_ = v_a_2157_;
v_isShared_2171_ = v_isSharedCheck_2202_;
goto v_resetjp_2169_;
}
else
{
lean_dec(v_a_2157_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2202_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2172_ = lean_unsigned_to_nat(1u);
v___x_2173_ = lean_nat_add(v_idx_2159_, v___x_2172_);
lean_dec(v_idx_2159_);
v___x_2174_ = lean_nat_dec_lt(v___x_2173_, v___x_2160_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2176_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v___x_2173_);
v___x_2176_ = v___x_2170_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_array_2158_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___x_2173_);
v___x_2176_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_box(0);
v___x_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
return v___x_2178_;
}
}
else
{
uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2180_ = lean_byte_array_fget(v_array_2158_, v___x_2173_);
v___x_2181_ = lean_nat_add(v___x_2173_, v___x_2172_);
lean_dec(v___x_2173_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v___x_2181_);
v___x_2183_ = v___x_2170_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_array_2158_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; uint32_t v___x_2186_; uint32_t v___x_2193_; uint8_t v___x_2194_; 
v___x_2184_ = lean_box(v___x_2180_);
lean_inc_ref(v___x_2183_);
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = lean_uint8_to_uint32(v___x_2180_);
v___x_2193_ = 9;
v___x_2194_ = lean_uint32_dec_eq(v___x_2186_, v___x_2193_);
if (v___x_2194_ == 0)
{
uint32_t v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = 32;
v___x_2196_ = lean_uint32_dec_eq(v___x_2186_, v___x_2195_);
if (v___x_2196_ == 0)
{
uint32_t v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = 33;
v___x_2198_ = lean_uint32_dec_le(v___x_2197_, v___x_2186_);
if (v___x_2198_ == 0)
{
lean_dec_ref_known(v___x_2185_, 2);
goto v___jp_2187_;
}
else
{
uint32_t v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = 126;
v___x_2200_ = lean_uint32_dec_le(v___x_2186_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_dec_ref_known(v___x_2185_, 2);
goto v___jp_2187_;
}
else
{
lean_dec_ref(v___x_2183_);
return v___x_2185_;
}
}
}
else
{
lean_dec_ref(v___x_2183_);
return v___x_2185_;
}
}
else
{
lean_dec_ref(v___x_2183_);
return v___x_2185_;
}
v___jp_2187_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2188_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2189_ = l_Char_quote(v___x_2186_);
v___x_2190_ = lean_string_append(v___x_2188_, v___x_2189_);
lean_dec_ref(v___x_2189_);
v___x_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2183_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
return v___x_2192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2209_, lean_object* v_buf_2210_, lean_object* v_length_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v_array_2213_; lean_object* v_idx_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v_array_2213_ = lean_ctor_get(v_a_2212_, 0);
v_idx_2214_ = lean_ctor_get(v_a_2212_, 1);
v___x_2215_ = lean_byte_array_size(v_array_2213_);
v___x_2216_ = lean_nat_dec_lt(v_idx_2214_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v_length_2211_);
lean_dec_ref(v_buf_2210_);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_a_2212_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
return v___x_2218_;
}
else
{
lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2291_; 
lean_inc(v_idx_2214_);
lean_inc_ref(v_array_2213_);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_a_2212_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; lean_object* v_unused_2293_; 
v_unused_2292_ = lean_ctor_get(v_a_2212_, 1);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_a_2212_, 0);
lean_dec(v_unused_2293_);
v___x_2220_ = v_a_2212_;
v_isShared_2221_ = v_isSharedCheck_2291_;
goto v_resetjp_2219_;
}
else
{
lean_dec(v_a_2212_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2291_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
uint8_t v_c_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_it_x27_2226_; 
v_c_2222_ = lean_byte_array_fget(v_array_2213_, v_idx_2214_);
v___x_2223_ = lean_unsigned_to_nat(1u);
v___x_2224_ = lean_nat_add(v_idx_2214_, v___x_2223_);
lean_dec(v_idx_2214_);
lean_inc(v___x_2224_);
lean_inc_ref(v_array_2213_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v___x_2224_);
v_it_x27_2226_ = v___x_2220_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_array_2213_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2224_);
v_it_x27_2226_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
uint8_t v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = 34;
v___x_2242_ = lean_uint8_dec_eq(v_c_2222_, v___x_2241_);
if (v___x_2242_ == 0)
{
uint8_t v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = 92;
v___x_2244_ = lean_uint8_dec_eq(v_c_2222_, v___x_2243_);
if (v___x_2244_ == 0)
{
uint32_t v___x_2245_; uint32_t v___x_2251_; uint8_t v___x_2252_; 
lean_dec(v___x_2224_);
lean_dec_ref(v_array_2213_);
v___x_2245_ = lean_uint8_to_uint32(v_c_2222_);
v___x_2251_ = 9;
v___x_2252_ = lean_uint32_dec_eq(v___x_2245_, v___x_2251_);
if (v___x_2252_ == 0)
{
uint32_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = 32;
v___x_2254_ = lean_uint32_dec_eq(v___x_2245_, v___x_2253_);
if (v___x_2254_ == 0)
{
uint32_t v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = 33;
v___x_2256_ = lean_uint32_dec_eq(v___x_2245_, v___x_2255_);
if (v___x_2256_ == 0)
{
uint32_t v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = 35;
v___x_2258_ = lean_uint32_dec_le(v___x_2257_, v___x_2245_);
if (v___x_2258_ == 0)
{
goto v___jp_2246_;
}
else
{
uint32_t v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = 91;
v___x_2260_ = lean_uint32_dec_le(v___x_2245_, v___x_2259_);
if (v___x_2260_ == 0)
{
goto v___jp_2246_;
}
else
{
goto v___jp_2227_;
}
}
}
else
{
goto v___jp_2227_;
}
}
else
{
goto v___jp_2227_;
}
}
else
{
goto v___jp_2227_;
}
v___jp_2246_:
{
uint32_t v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = 93;
v___x_2248_ = lean_uint32_dec_le(v___x_2247_, v___x_2245_);
if (v___x_2248_ == 0)
{
lean_dec(v_length_2211_);
lean_dec_ref(v_buf_2210_);
goto v___jp_2234_;
}
else
{
uint32_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = 126;
v___x_2250_ = lean_uint32_dec_le(v___x_2245_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_dec(v_length_2211_);
lean_dec_ref(v_buf_2210_);
goto v___jp_2234_;
}
else
{
goto v___jp_2227_;
}
}
}
}
else
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_nat_dec_lt(v___x_2224_, v___x_2215_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec(v___x_2224_);
lean_dec_ref(v_array_2213_);
lean_dec(v_length_2211_);
lean_dec_ref(v_buf_2210_);
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2263_, 0, v_it_x27_2226_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
return v___x_2263_;
}
else
{
uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint32_t v___x_2274_; uint32_t v___x_2281_; uint8_t v___x_2282_; 
lean_dec_ref(v_it_x27_2226_);
v___x_2264_ = lean_byte_array_fget(v_array_2213_, v___x_2224_);
v___x_2265_ = lean_nat_add(v___x_2224_, v___x_2223_);
lean_dec(v___x_2224_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v_array_2213_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2274_ = lean_uint8_to_uint32(v___x_2264_);
v___x_2281_ = 9;
v___x_2282_ = lean_uint32_dec_eq(v___x_2274_, v___x_2281_);
if (v___x_2282_ == 0)
{
uint32_t v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = 32;
v___x_2284_ = lean_uint32_dec_eq(v___x_2274_, v___x_2283_);
if (v___x_2284_ == 0)
{
uint32_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = 33;
v___x_2286_ = lean_uint32_dec_le(v___x_2285_, v___x_2274_);
if (v___x_2286_ == 0)
{
lean_dec(v_length_2211_);
lean_dec_ref(v_buf_2210_);
goto v___jp_2275_;
}
else
{
uint32_t v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = 126;
v___x_2288_ = lean_uint32_dec_le(v___x_2274_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_dec(v_length_2211_);
lean_dec_ref(v_buf_2210_);
goto v___jp_2275_;
}
else
{
goto v___jp_2267_;
}
}
}
else
{
goto v___jp_2267_;
}
}
else
{
goto v___jp_2267_;
}
v___jp_2267_:
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = lean_nat_add(v_length_2211_, v___x_2223_);
lean_dec(v_length_2211_);
v___x_2269_ = lean_nat_dec_lt(v_maxLength_2209_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_byte_array_push(v_buf_2210_, v___x_2264_);
v_buf_2210_ = v___x_2270_;
v_length_2211_ = v___x_2268_;
v_a_2212_ = v___x_2266_;
goto _start;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v___x_2268_);
lean_dec_ref(v_buf_2210_);
v___x_2272_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2266_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
return v___x_2273_;
}
}
v___jp_2275_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2276_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2277_ = l_Char_quote(v___x_2274_);
v___x_2278_ = lean_string_append(v___x_2276_, v___x_2277_);
lean_dec_ref(v___x_2277_);
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2266_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
return v___x_2280_;
}
}
}
}
else
{
lean_object* v___x_2289_; 
lean_dec(v___x_2224_);
lean_dec_ref(v_array_2213_);
lean_dec(v_length_2211_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_it_x27_2226_);
lean_ctor_set(v___x_2289_, 1, v_buf_2210_);
return v___x_2289_;
}
v___jp_2227_:
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = lean_nat_add(v_length_2211_, v___x_2223_);
lean_dec(v_length_2211_);
v___x_2229_ = lean_nat_dec_lt(v_maxLength_2209_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_byte_array_push(v_buf_2210_, v_c_2222_);
v_buf_2210_ = v___x_2230_;
v_length_2211_ = v___x_2228_;
v_a_2212_ = v_it_x27_2226_;
goto _start;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v___x_2228_);
lean_dec_ref(v_buf_2210_);
v___x_2232_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_it_x27_2226_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
return v___x_2233_;
}
}
v___jp_2234_:
{
lean_object* v___x_2235_; uint32_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2235_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2236_ = lean_uint8_to_uint32(v_c_2222_);
v___x_2237_ = l_Char_quote(v___x_2236_);
v___x_2238_ = lean_string_append(v___x_2235_, v___x_2237_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_it_x27_2226_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
return v___x_2240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2294_, lean_object* v_buf_2295_, lean_object* v_length_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2294_, v_buf_2295_, v_length_2296_, v_a_2297_);
lean_dec(v_maxLength_2294_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_array_2304_; lean_object* v_idx_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v_array_2304_ = lean_ctor_get(v_a_2303_, 0);
v_idx_2305_ = lean_ctor_get(v_a_2303_, 1);
v___x_2306_ = lean_byte_array_size(v_array_2304_);
v___x_2307_ = lean_nat_dec_lt(v_idx_2305_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_box(0);
v___x_2309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2309_, 0, v_a_2303_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
return v___x_2309_;
}
else
{
uint8_t v___x_2310_; uint8_t v_got_2311_; uint8_t v___x_2312_; 
v___x_2310_ = 34;
v_got_2311_ = lean_byte_array_fget(v_array_2304_, v_idx_2305_);
v___x_2312_ = lean_uint8_dec_eq(v_got_2311_, v___x_2310_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2314_, 0, v_a_2303_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
return v___x_2314_;
}
else
{
lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2343_; 
lean_inc(v_idx_2305_);
lean_inc_ref(v_array_2304_);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_a_2303_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; lean_object* v_unused_2345_; 
v_unused_2344_ = lean_ctor_get(v_a_2303_, 1);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_a_2303_, 0);
lean_dec(v_unused_2345_);
v___x_2316_ = v_a_2303_;
v_isShared_2317_ = v_isSharedCheck_2343_;
goto v_resetjp_2315_;
}
else
{
lean_dec(v_a_2303_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2343_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_add(v_idx_2305_, v___x_2318_);
lean_dec(v_idx_2305_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 1, v___x_2319_);
v___x_2321_ = v___x_2316_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_array_2304_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = l_ByteArray_empty;
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2302_, v___x_2322_, v___x_2323_, v___x_2321_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_pos_2325_; lean_object* v_res_2326_; uint8_t v___x_2327_; 
v_pos_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_pos_2325_);
v_res_2326_ = lean_ctor_get(v___x_2324_, 1);
lean_inc(v_res_2326_);
lean_dec_ref_known(v___x_2324_, 2);
v___x_2327_ = lean_string_validate_utf8(v_res_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_res_2326_);
v___x_2328_ = lean_box(0);
v___x_2329_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2328_, v_pos_2325_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = lean_string_from_utf8_unchecked(v_res_2326_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
v___x_2332_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2331_, v_pos_2325_);
lean_dec_ref_known(v___x_2331_, 1);
return v___x_2332_;
}
}
else
{
lean_object* v_pos_2333_; lean_object* v_err_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_pos_2333_ = lean_ctor_get(v___x_2324_, 0);
v_err_2334_ = lean_ctor_get(v___x_2324_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2324_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_err_2334_);
lean_inc(v_pos_2333_);
lean_dec(v___x_2324_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_pos_2333_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_err_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_2346_, v_a_2347_);
lean_dec(v_maxLength_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_2349_, lean_object* v_maxSpaceSequence_2350_, lean_object* v_x_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_pos_2354_; lean_object* v_pos_2358_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_snd_2363_; lean_object* v_snd_2364_; uint8_t v___x_2365_; 
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2349_, v_maxSpaceSequence_2350_, v___x_2361_, v___y_2352_);
v_snd_2363_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_snd_2363_);
lean_dec_ref(v___x_2362_);
v_snd_2364_ = lean_ctor_get(v_snd_2363_, 1);
v___x_2365_ = lean_unbox(v_snd_2364_);
if (v___x_2365_ == 0)
{
lean_object* v_fst_2366_; lean_object* v_array_2367_; lean_object* v_idx_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_fst_2366_ = lean_ctor_get(v_snd_2363_, 0);
lean_inc(v_fst_2366_);
lean_dec(v_snd_2363_);
v_array_2367_ = lean_ctor_get(v_fst_2366_, 0);
v_idx_2368_ = lean_ctor_get(v_fst_2366_, 1);
v___x_2369_ = lean_byte_array_size(v_array_2367_);
v___x_2370_ = lean_nat_dec_lt(v_idx_2368_, v___x_2369_);
if (v___x_2370_ == 0)
{
v_pos_2354_ = v_fst_2366_;
goto v___jp_2353_;
}
else
{
uint8_t v___x_2371_; uint32_t v___x_2372_; uint32_t v___x_2373_; uint8_t v___x_2374_; 
v___x_2371_ = lean_byte_array_fget(v_array_2367_, v_idx_2368_);
v___x_2372_ = lean_uint8_to_uint32(v___x_2371_);
v___x_2373_ = 32;
v___x_2374_ = lean_uint32_dec_eq(v___x_2372_, v___x_2373_);
if (v___x_2374_ == 0)
{
uint32_t v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = 9;
v___x_2376_ = lean_uint32_dec_eq(v___x_2372_, v___x_2375_);
if (v___x_2376_ == 0)
{
v_pos_2354_ = v_fst_2366_;
goto v___jp_2353_;
}
else
{
v_pos_2358_ = v_fst_2366_;
goto v___jp_2357_;
}
}
else
{
v_pos_2358_ = v_fst_2366_;
goto v___jp_2357_;
}
}
}
else
{
lean_object* v_fst_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2385_; 
v_fst_2377_ = lean_ctor_get(v_snd_2363_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_snd_2363_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v_snd_2363_, 1);
lean_dec(v_unused_2386_);
v___x_2379_ = v_snd_2363_;
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_fst_2377_);
lean_dec(v_snd_2363_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2381_ = lean_box(0);
if (v_isShared_2380_ == 0)
{
lean_ctor_set_tag(v___x_2379_, 1);
lean_ctor_set(v___x_2379_, 1, v___x_2381_);
v___x_2383_ = v___x_2379_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_fst_2377_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
v___jp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2356_, 0, v_pos_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
return v___x_2356_;
}
v___jp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_pos_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_2387_, lean_object* v_maxSpaceSequence_2388_, lean_object* v_x_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2387_, v_maxSpaceSequence_2388_, v_x_2389_, v___y_2390_);
lean_dec(v_maxSpaceSequence_2388_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_pos_2407_; lean_object* v_pos_2411_; lean_object* v___y_2415_; lean_object* v_pos_2416_; lean_object* v___y_2421_; lean_object* v_pos_2422_; lean_object* v_res_2423_; lean_object* v___y_2430_; lean_object* v_pos_2431_; lean_object* v_res_2432_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v_lower_2449_; lean_object* v_upper_2450_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v_pos_2466_; lean_object* v_pos_2470_; lean_object* v_maxSpaceSequence_2473_; lean_object* v_maxChunkExtNameLength_2474_; lean_object* v_maxChunkExtValueLength_2475_; lean_object* v___f_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_snd_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2771_; 
v_maxSpaceSequence_2473_ = lean_ctor_get(v_limits_2404_, 8);
v_maxChunkExtNameLength_2474_ = lean_ctor_get(v_limits_2404_, 11);
v_maxChunkExtValueLength_2475_ = lean_ctor_get(v_limits_2404_, 12);
v___f_2476_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2476_, v_maxSpaceSequence_2473_, v___x_2477_, v_a_2405_);
v_snd_2479_ = lean_ctor_get(v___x_2478_, 1);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v___x_2478_, 0);
lean_dec(v_unused_2772_);
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2771_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_snd_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2771_;
goto v_resetjp_2480_;
}
v___jp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_pos_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
return v___x_2409_;
}
v___jp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2413_, 0, v_pos_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
return v___x_2413_;
}
v___jp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = lean_box(0);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___y_2415_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v_pos_2416_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
return v___x_2419_;
}
v___jp_2420_:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_2423_);
if (lean_obj_tag(v___x_2424_) == 1)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___y_2421_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v_pos_2422_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec(v___x_2424_);
lean_dec_ref(v___y_2421_);
v___x_2427_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
v___x_2428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2428_, 0, v_pos_2422_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
return v___x_2428_;
}
}
v___jp_2429_:
{
lean_object* v___x_2433_; 
v___x_2433_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2432_, v_pos_2431_);
lean_dec(v_res_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_pos_2434_; lean_object* v_res_2435_; 
v_pos_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_pos_2434_);
v_res_2435_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_res_2435_);
lean_dec_ref_known(v___x_2433_, 2);
v___y_2421_ = v___y_2430_;
v_pos_2422_ = v_pos_2434_;
v_res_2423_ = v_res_2435_;
goto v___jp_2420_;
}
else
{
lean_object* v_pos_2436_; lean_object* v_err_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v___y_2430_);
v_pos_2436_ = lean_ctor_get(v___x_2433_, 0);
v_err_2437_ = lean_ctor_get(v___x_2433_, 1);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2433_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_err_2437_);
lean_inc(v_pos_2436_);
lean_dec(v___x_2433_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_pos_2436_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_err_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
v___jp_2445_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2451_ = l_ByteArray_toByteSlice(v___y_2447_, v_lower_2449_, v_upper_2450_);
v___x_2452_ = l_ByteSlice_toByteArray(v___x_2451_);
v___x_2453_ = lean_string_validate_utf8(v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec_ref(v___x_2452_);
v___x_2454_ = lean_box(0);
v___y_2430_ = v___y_2448_;
v_pos_2431_ = v___y_2446_;
v_res_2432_ = v___x_2454_;
goto v___jp_2429_;
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = lean_string_from_utf8_unchecked(v___x_2452_);
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
v___y_2430_ = v___y_2448_;
v_pos_2431_ = v___y_2446_;
v_res_2432_ = v___x_2456_;
goto v___jp_2429_;
}
}
v___jp_2457_:
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_nat_dec_le(v___y_2461_, v___y_2462_);
if (v___x_2464_ == 0)
{
lean_dec(v___y_2461_);
v___y_2446_ = v___y_2458_;
v___y_2447_ = v___y_2459_;
v___y_2448_ = v___y_2460_;
v_lower_2449_ = v___y_2463_;
v_upper_2450_ = v___y_2462_;
goto v___jp_2445_;
}
else
{
lean_dec(v___y_2462_);
v___y_2446_ = v___y_2458_;
v___y_2447_ = v___y_2459_;
v___y_2448_ = v___y_2460_;
v_lower_2449_ = v___y_2463_;
v_upper_2450_ = v___y_2461_;
goto v___jp_2445_;
}
}
v___jp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_pos_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
return v___x_2468_;
}
v___jp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v_pos_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
return v___x_2472_;
}
v_resetjp_2480_:
{
lean_object* v_snd_2483_; uint8_t v___x_2484_; 
v_snd_2483_ = lean_ctor_get(v_snd_2479_, 1);
v___x_2484_ = lean_unbox(v_snd_2483_);
if (v___x_2484_ == 0)
{
lean_object* v_fst_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2759_; 
v_fst_2485_ = lean_ctor_get(v_snd_2479_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_snd_2479_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v_snd_2479_, 1);
lean_dec(v_unused_2760_);
v___x_2487_ = v_snd_2479_;
v_isShared_2488_ = v_isSharedCheck_2759_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_fst_2485_);
lean_dec(v_snd_2479_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2759_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_array_2489_; lean_object* v_idx_2490_; lean_object* v___f_2491_; lean_object* v___y_2493_; lean_object* v_pos_2494_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v_pos_2533_; lean_object* v_array_2534_; lean_object* v_idx_2535_; lean_object* v_pos_2591_; lean_object* v_res_2592_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v_lower_2658_; lean_object* v_upper_2659_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v_pos_2674_; lean_object* v_pos_2707_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v_array_2489_ = lean_ctor_get(v_fst_2485_, 0);
v_idx_2490_ = lean_ctor_get(v_fst_2485_, 1);
v___f_2491_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2751_ = lean_byte_array_size(v_array_2489_);
v___x_2752_ = lean_nat_dec_lt(v_idx_2490_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_inc(v_idx_2490_);
lean_inc_ref(v_array_2489_);
v_pos_2707_ = v_fst_2485_;
goto v___jp_2706_;
}
else
{
uint8_t v___x_2753_; uint32_t v___x_2754_; uint32_t v___x_2755_; uint8_t v___x_2756_; 
v___x_2753_ = lean_byte_array_fget(v_array_2489_, v_idx_2490_);
v___x_2754_ = lean_uint8_to_uint32(v___x_2753_);
v___x_2755_ = 32;
v___x_2756_ = lean_uint32_dec_eq(v___x_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
uint32_t v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = 9;
v___x_2758_ = lean_uint32_dec_eq(v___x_2754_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_inc(v_idx_2490_);
lean_inc_ref(v_array_2489_);
v_pos_2707_ = v_fst_2485_;
goto v___jp_2706_;
}
else
{
lean_del_object(v___x_2487_);
lean_del_object(v___x_2481_);
v_pos_2407_ = v_fst_2485_;
goto v___jp_2406_;
}
}
else
{
lean_del_object(v___x_2487_);
lean_del_object(v___x_2481_);
v_pos_2407_ = v_fst_2485_;
goto v___jp_2406_;
}
}
v___jp_2492_:
{
lean_object* v___x_2495_; 
lean_inc_ref(v_pos_2494_);
v___x_2495_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_2475_, v_pos_2494_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_pos_2496_; lean_object* v_res_2497_; 
lean_dec_ref(v_pos_2494_);
v_pos_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_pos_2496_);
v_res_2497_ = lean_ctor_get(v___x_2495_, 1);
lean_inc(v_res_2497_);
lean_dec_ref_known(v___x_2495_, 2);
v___y_2421_ = v___y_2493_;
v_pos_2422_ = v_pos_2496_;
v_res_2423_ = v_res_2497_;
goto v___jp_2420_;
}
else
{
lean_object* v_pos_2498_; lean_object* v_err_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2529_; 
v_pos_2498_ = lean_ctor_get(v___x_2495_, 0);
v_err_2499_ = lean_ctor_get(v___x_2495_, 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2501_ = v___x_2495_;
v_isShared_2502_ = v_isSharedCheck_2529_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_err_2499_);
lean_inc(v_pos_2498_);
lean_dec(v___x_2495_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2529_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_idx_2503_; lean_object* v_array_2504_; lean_object* v_idx_2505_; uint8_t v___x_2506_; 
v_idx_2503_ = lean_ctor_get(v_pos_2494_, 1);
lean_inc(v_idx_2503_);
lean_dec_ref(v_pos_2494_);
v_array_2504_ = lean_ctor_get(v_pos_2498_, 0);
v_idx_2505_ = lean_ctor_get(v_pos_2498_, 1);
v___x_2506_ = lean_nat_dec_eq(v_idx_2503_, v_idx_2505_);
lean_dec(v_idx_2503_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2508_; 
lean_dec_ref(v___y_2493_);
if (v_isShared_2502_ == 0)
{
v___x_2508_ = v___x_2501_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_pos_2498_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_err_2499_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
else
{
lean_object* v___x_2510_; lean_object* v_snd_2511_; lean_object* v_snd_2512_; uint8_t v___x_2513_; 
lean_dec(v_err_2499_);
lean_inc(v_pos_2498_);
v___x_2510_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2491_, v_maxChunkExtValueLength_2475_, v___x_2477_, v_pos_2498_);
v_snd_2511_ = lean_ctor_get(v___x_2510_, 1);
lean_inc(v_snd_2511_);
v_snd_2512_ = lean_ctor_get(v_snd_2511_, 1);
v___x_2513_ = lean_unbox(v_snd_2512_);
if (v___x_2513_ == 0)
{
lean_object* v_fst_2514_; lean_object* v_fst_2515_; uint8_t v___x_2516_; 
v_fst_2514_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_fst_2514_);
lean_dec_ref(v___x_2510_);
v_fst_2515_ = lean_ctor_get(v_snd_2511_, 0);
lean_inc(v_fst_2515_);
lean_dec(v_snd_2511_);
v___x_2516_ = lean_nat_dec_eq(v_fst_2514_, v___x_2477_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
lean_inc(v_idx_2505_);
lean_inc_ref(v_array_2504_);
lean_del_object(v___x_2501_);
lean_dec(v_pos_2498_);
v___x_2517_ = lean_nat_add(v_idx_2505_, v_fst_2514_);
lean_dec(v_fst_2514_);
v___x_2518_ = lean_byte_array_size(v_array_2504_);
v___x_2519_ = lean_nat_dec_le(v_idx_2505_, v___x_2477_);
if (v___x_2519_ == 0)
{
v___y_2458_ = v_fst_2515_;
v___y_2459_ = v_array_2504_;
v___y_2460_ = v___y_2493_;
v___y_2461_ = v___x_2517_;
v___y_2462_ = v___x_2518_;
v___y_2463_ = v_idx_2505_;
goto v___jp_2457_;
}
else
{
lean_dec(v_idx_2505_);
v___y_2458_ = v_fst_2515_;
v___y_2459_ = v_array_2504_;
v___y_2460_ = v___y_2493_;
v___y_2461_ = v___x_2517_;
v___y_2462_ = v___x_2518_;
v___y_2463_ = v___x_2477_;
goto v___jp_2457_;
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
lean_dec(v_fst_2515_);
lean_dec(v_fst_2514_);
lean_dec_ref(v___y_2493_);
v___x_2520_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2520_);
v___x_2522_ = v___x_2501_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_pos_2498_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
else
{
lean_object* v_fst_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
lean_dec_ref(v___x_2510_);
lean_dec(v_pos_2498_);
lean_dec_ref(v___y_2493_);
v_fst_2524_ = lean_ctor_get(v_snd_2511_, 0);
lean_inc(v_fst_2524_);
lean_dec(v_snd_2511_);
v___x_2525_ = lean_box(0);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2525_);
lean_ctor_set(v___x_2501_, 0, v_fst_2524_);
v___x_2527_ = v___x_2501_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_fst_2524_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
v___jp_2530_:
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = lean_byte_array_size(v_array_2534_);
v___x_2537_ = lean_nat_dec_lt(v_idx_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_dec(v_idx_2535_);
lean_dec_ref(v_array_2534_);
lean_dec_ref(v___y_2531_);
v___x_2538_ = lean_box(0);
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 1);
lean_ctor_set(v___x_2487_, 1, v___x_2538_);
lean_ctor_set(v___x_2487_, 0, v_pos_2533_);
v___x_2540_ = v___x_2487_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_pos_2533_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
else
{
uint8_t v___x_2542_; uint8_t v_got_2543_; uint8_t v___x_2544_; 
v___x_2542_ = 61;
v_got_2543_ = lean_byte_array_fget(v_array_2534_, v_idx_2535_);
v___x_2544_ = lean_uint8_dec_eq(v_got_2543_, v___x_2542_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_dec(v_idx_2535_);
lean_dec_ref(v_array_2534_);
lean_dec_ref(v___y_2531_);
v___x_2545_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 1);
lean_ctor_set(v___x_2487_, 1, v___x_2545_);
lean_ctor_set(v___x_2487_, 0, v_pos_2533_);
v___x_2547_ = v___x_2487_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_pos_2533_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
lean_dec_ref(v_pos_2533_);
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = lean_nat_add(v_idx_2535_, v___x_2549_);
lean_dec(v_idx_2535_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v___x_2550_);
lean_ctor_set(v___x_2487_, 0, v_array_2534_);
v___x_2552_ = v___x_2487_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_array_2534_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2553_; 
v___x_2553_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2476_, v_maxSpaceSequence_2473_, v___y_2532_, v___x_2552_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_pos_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2578_; 
v_pos_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; 
v_unused_2579_ = lean_ctor_get(v___x_2553_, 1);
lean_dec(v_unused_2579_);
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2578_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_pos_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2578_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v_snd_2559_; lean_object* v_snd_2560_; uint8_t v___x_2561_; 
v___x_2558_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2476_, v_maxSpaceSequence_2473_, v___x_2477_, v_pos_2554_);
v_snd_2559_ = lean_ctor_get(v___x_2558_, 1);
lean_inc(v_snd_2559_);
lean_dec_ref(v___x_2558_);
v_snd_2560_ = lean_ctor_get(v_snd_2559_, 1);
v___x_2561_ = lean_unbox(v_snd_2560_);
if (v___x_2561_ == 0)
{
lean_object* v_fst_2562_; lean_object* v_array_2563_; lean_object* v_idx_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
lean_del_object(v___x_2556_);
v_fst_2562_ = lean_ctor_get(v_snd_2559_, 0);
lean_inc(v_fst_2562_);
lean_dec(v_snd_2559_);
v_array_2563_ = lean_ctor_get(v_fst_2562_, 0);
v_idx_2564_ = lean_ctor_get(v_fst_2562_, 1);
v___x_2565_ = lean_byte_array_size(v_array_2563_);
v___x_2566_ = lean_nat_dec_lt(v_idx_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
v___y_2493_ = v___y_2531_;
v_pos_2494_ = v_fst_2562_;
goto v___jp_2492_;
}
else
{
uint8_t v___x_2567_; uint32_t v___x_2568_; uint32_t v___x_2569_; uint8_t v___x_2570_; 
v___x_2567_ = lean_byte_array_fget(v_array_2563_, v_idx_2564_);
v___x_2568_ = lean_uint8_to_uint32(v___x_2567_);
v___x_2569_ = 32;
v___x_2570_ = lean_uint32_dec_eq(v___x_2568_, v___x_2569_);
if (v___x_2570_ == 0)
{
uint32_t v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = 9;
v___x_2572_ = lean_uint32_dec_eq(v___x_2568_, v___x_2571_);
if (v___x_2572_ == 0)
{
v___y_2493_ = v___y_2531_;
v_pos_2494_ = v_fst_2562_;
goto v___jp_2492_;
}
else
{
lean_dec_ref(v___y_2531_);
v_pos_2466_ = v_fst_2562_;
goto v___jp_2465_;
}
}
else
{
lean_dec_ref(v___y_2531_);
v_pos_2466_ = v_fst_2562_;
goto v___jp_2465_;
}
}
}
else
{
lean_object* v_fst_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_dec_ref(v___y_2531_);
v_fst_2573_ = lean_ctor_get(v_snd_2559_, 0);
lean_inc(v_fst_2573_);
lean_dec(v_snd_2559_);
v___x_2574_ = lean_box(0);
if (v_isShared_2557_ == 0)
{
lean_ctor_set_tag(v___x_2556_, 1);
lean_ctor_set(v___x_2556_, 1, v___x_2574_);
lean_ctor_set(v___x_2556_, 0, v_fst_2573_);
v___x_2576_ = v___x_2556_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_fst_2573_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_object* v_pos_2580_; lean_object* v_err_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec_ref(v___y_2531_);
v_pos_2580_ = lean_ctor_get(v___x_2553_, 0);
v_err_2581_ = lean_ctor_get(v___x_2553_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2553_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_err_2581_);
lean_inc(v_pos_2580_);
lean_dec(v___x_2553_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_pos_2580_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_err_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
}
}
v___jp_2590_:
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2592_, v_pos_2591_);
lean_dec(v_res_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_pos_2594_; lean_object* v_res_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_pos_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_pos_2594_);
v_res_2595_ = lean_ctor_get(v___x_2593_, 1);
lean_inc(v_res_2595_);
lean_dec_ref_known(v___x_2593_, 2);
v___x_2596_ = lean_box(0);
v___x_2597_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2476_, v_maxSpaceSequence_2473_, v___x_2596_, v_pos_2594_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_pos_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2635_; 
v_pos_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v___x_2597_, 1);
lean_dec(v_unused_2636_);
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2635_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_pos_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2635_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_2595_);
if (lean_obj_tag(v___x_2602_) == 1)
{
lean_object* v_val_2603_; lean_object* v_array_2604_; lean_object* v_idx_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v_val_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v_array_2604_ = lean_ctor_get(v_pos_2598_, 0);
v_idx_2605_ = lean_ctor_get(v_pos_2598_, 1);
v___x_2606_ = lean_byte_array_size(v_array_2604_);
v___x_2607_ = lean_nat_dec_lt(v_idx_2605_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_del_object(v___x_2600_);
lean_del_object(v___x_2487_);
v___y_2415_ = v_val_2603_;
v_pos_2416_ = v_pos_2598_;
goto v___jp_2414_;
}
else
{
uint8_t v___x_2608_; uint8_t v___x_2609_; uint8_t v___x_2610_; 
v___x_2608_ = lean_byte_array_fget(v_array_2604_, v_idx_2605_);
v___x_2609_ = 61;
v___x_2610_ = lean_uint8_dec_eq(v___x_2608_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_del_object(v___x_2600_);
lean_del_object(v___x_2487_);
v___y_2415_ = v_val_2603_;
v_pos_2416_ = v_pos_2598_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2611_; lean_object* v_snd_2612_; lean_object* v_snd_2613_; uint8_t v___x_2614_; 
v___x_2611_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2476_, v_maxSpaceSequence_2473_, v___x_2477_, v_pos_2598_);
v_snd_2612_ = lean_ctor_get(v___x_2611_, 1);
lean_inc(v_snd_2612_);
lean_dec_ref(v___x_2611_);
v_snd_2613_ = lean_ctor_get(v_snd_2612_, 1);
v___x_2614_ = lean_unbox(v_snd_2613_);
if (v___x_2614_ == 0)
{
lean_object* v_fst_2615_; lean_object* v_array_2616_; lean_object* v_idx_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
lean_del_object(v___x_2600_);
v_fst_2615_ = lean_ctor_get(v_snd_2612_, 0);
lean_inc(v_fst_2615_);
lean_dec(v_snd_2612_);
v_array_2616_ = lean_ctor_get(v_fst_2615_, 0);
v_idx_2617_ = lean_ctor_get(v_fst_2615_, 1);
v___x_2618_ = lean_byte_array_size(v_array_2616_);
v___x_2619_ = lean_nat_dec_lt(v_idx_2617_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_inc(v_idx_2617_);
lean_inc_ref(v_array_2616_);
v___y_2531_ = v_val_2603_;
v___y_2532_ = v___x_2596_;
v_pos_2533_ = v_fst_2615_;
v_array_2534_ = v_array_2616_;
v_idx_2535_ = v_idx_2617_;
goto v___jp_2530_;
}
else
{
uint8_t v___x_2620_; uint32_t v___x_2621_; uint32_t v___x_2622_; uint8_t v___x_2623_; 
v___x_2620_ = lean_byte_array_fget(v_array_2616_, v_idx_2617_);
v___x_2621_ = lean_uint8_to_uint32(v___x_2620_);
v___x_2622_ = 32;
v___x_2623_ = lean_uint32_dec_eq(v___x_2621_, v___x_2622_);
if (v___x_2623_ == 0)
{
uint32_t v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = 9;
v___x_2625_ = lean_uint32_dec_eq(v___x_2621_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_inc(v_idx_2617_);
lean_inc_ref(v_array_2616_);
v___y_2531_ = v_val_2603_;
v___y_2532_ = v___x_2596_;
v_pos_2533_ = v_fst_2615_;
v_array_2534_ = v_array_2616_;
v_idx_2535_ = v_idx_2617_;
goto v___jp_2530_;
}
else
{
lean_dec(v_val_2603_);
lean_del_object(v___x_2487_);
v_pos_2470_ = v_fst_2615_;
goto v___jp_2469_;
}
}
else
{
lean_dec(v_val_2603_);
lean_del_object(v___x_2487_);
v_pos_2470_ = v_fst_2615_;
goto v___jp_2469_;
}
}
}
else
{
lean_object* v_fst_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
lean_dec(v_val_2603_);
lean_del_object(v___x_2487_);
v_fst_2626_ = lean_ctor_get(v_snd_2612_, 0);
lean_inc(v_fst_2626_);
lean_dec(v_snd_2612_);
v___x_2627_ = lean_box(0);
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 1);
lean_ctor_set(v___x_2600_, 1, v___x_2627_);
lean_ctor_set(v___x_2600_, 0, v_fst_2626_);
v___x_2629_ = v___x_2600_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_fst_2626_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
lean_dec(v___x_2602_);
lean_del_object(v___x_2487_);
v___x_2631_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 1);
lean_ctor_set(v___x_2600_, 1, v___x_2631_);
v___x_2633_ = v___x_2600_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_pos_2598_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v_pos_2637_; lean_object* v_err_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_res_2595_);
lean_del_object(v___x_2487_);
v_pos_2637_ = lean_ctor_get(v___x_2597_, 0);
v_err_2638_ = lean_ctor_get(v___x_2597_, 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2597_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_err_2638_);
lean_inc(v_pos_2637_);
lean_dec(v___x_2597_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_pos_2637_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_err_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_pos_2646_; lean_object* v_err_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_del_object(v___x_2487_);
v_pos_2646_ = lean_ctor_get(v___x_2593_, 0);
v_err_2647_ = lean_ctor_get(v___x_2593_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2593_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_err_2647_);
lean_inc(v_pos_2646_);
lean_dec(v___x_2593_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_pos_2646_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_err_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
v___jp_2655_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2660_ = l_ByteArray_toByteSlice(v___y_2656_, v_lower_2658_, v_upper_2659_);
v___x_2661_ = l_ByteSlice_toByteArray(v___x_2660_);
v___x_2662_ = lean_string_validate_utf8(v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; 
lean_dec_ref(v___x_2661_);
v___x_2663_ = lean_box(0);
v_pos_2591_ = v___y_2657_;
v_res_2592_ = v___x_2663_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_string_from_utf8_unchecked(v___x_2661_);
v___x_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
v_pos_2591_ = v___y_2657_;
v_res_2592_ = v___x_2665_;
goto v___jp_2590_;
}
}
v___jp_2666_:
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_nat_dec_le(v___y_2670_, v___y_2669_);
if (v___x_2672_ == 0)
{
lean_dec(v___y_2670_);
v___y_2656_ = v___y_2667_;
v___y_2657_ = v___y_2668_;
v_lower_2658_ = v___y_2671_;
v_upper_2659_ = v___y_2669_;
goto v___jp_2655_;
}
else
{
lean_dec(v___y_2669_);
v___y_2656_ = v___y_2667_;
v___y_2657_ = v___y_2668_;
v_lower_2658_ = v___y_2671_;
v_upper_2659_ = v___y_2670_;
goto v___jp_2655_;
}
}
v___jp_2673_:
{
lean_object* v___x_2675_; lean_object* v_snd_2676_; lean_object* v_snd_2677_; uint8_t v___x_2678_; 
lean_inc_ref(v_pos_2674_);
v___x_2675_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2491_, v_maxChunkExtNameLength_2474_, v___x_2477_, v_pos_2674_);
v_snd_2676_ = lean_ctor_get(v___x_2675_, 1);
lean_inc(v_snd_2676_);
v_snd_2677_ = lean_ctor_get(v_snd_2676_, 1);
v___x_2678_ = lean_unbox(v_snd_2677_);
if (v___x_2678_ == 0)
{
lean_object* v_fst_2679_; lean_object* v_fst_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2694_; 
v_fst_2679_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_fst_2679_);
lean_dec_ref(v___x_2675_);
v_fst_2680_ = lean_ctor_get(v_snd_2676_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_snd_2676_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v_snd_2676_, 1);
lean_dec(v_unused_2695_);
v___x_2682_ = v_snd_2676_;
v_isShared_2683_ = v_isSharedCheck_2694_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_fst_2680_);
lean_dec(v_snd_2676_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2694_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
uint8_t v___x_2684_; 
v___x_2684_ = lean_nat_dec_eq(v_fst_2679_, v___x_2477_);
if (v___x_2684_ == 0)
{
lean_object* v_array_2685_; lean_object* v_idx_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
lean_del_object(v___x_2682_);
v_array_2685_ = lean_ctor_get(v_pos_2674_, 0);
lean_inc_ref(v_array_2685_);
v_idx_2686_ = lean_ctor_get(v_pos_2674_, 1);
lean_inc(v_idx_2686_);
lean_dec_ref(v_pos_2674_);
v___x_2687_ = lean_nat_add(v_idx_2686_, v_fst_2679_);
lean_dec(v_fst_2679_);
v___x_2688_ = lean_byte_array_size(v_array_2685_);
v___x_2689_ = lean_nat_dec_le(v_idx_2686_, v___x_2477_);
if (v___x_2689_ == 0)
{
v___y_2667_ = v_array_2685_;
v___y_2668_ = v_fst_2680_;
v___y_2669_ = v___x_2688_;
v___y_2670_ = v___x_2687_;
v___y_2671_ = v_idx_2686_;
goto v___jp_2666_;
}
else
{
lean_dec(v_idx_2686_);
v___y_2667_ = v_array_2685_;
v___y_2668_ = v_fst_2680_;
v___y_2669_ = v___x_2688_;
v___y_2670_ = v___x_2687_;
v___y_2671_ = v___x_2477_;
goto v___jp_2666_;
}
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
lean_dec(v_fst_2680_);
lean_dec(v_fst_2679_);
lean_del_object(v___x_2487_);
v___x_2690_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2683_ == 0)
{
lean_ctor_set_tag(v___x_2682_, 1);
lean_ctor_set(v___x_2682_, 1, v___x_2690_);
lean_ctor_set(v___x_2682_, 0, v_pos_2674_);
v___x_2692_ = v___x_2682_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_pos_2674_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
else
{
lean_object* v_fst_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v___x_2675_);
lean_dec_ref(v_pos_2674_);
lean_del_object(v___x_2487_);
v_fst_2696_ = lean_ctor_get(v_snd_2676_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_snd_2676_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v_snd_2676_, 1);
lean_dec(v_unused_2705_);
v___x_2698_ = v_snd_2676_;
v_isShared_2699_ = v_isSharedCheck_2704_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_fst_2696_);
lean_dec(v_snd_2676_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2704_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = lean_box(0);
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 1);
lean_ctor_set(v___x_2698_, 1, v___x_2700_);
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_fst_2696_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
v___jp_2706_:
{
lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = lean_byte_array_size(v_array_2489_);
v___x_2709_ = lean_nat_dec_lt(v_idx_2490_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2712_; 
lean_dec(v_idx_2490_);
lean_dec_ref(v_array_2489_);
lean_del_object(v___x_2487_);
v___x_2710_ = lean_box(0);
if (v_isShared_2482_ == 0)
{
lean_ctor_set_tag(v___x_2481_, 1);
lean_ctor_set(v___x_2481_, 1, v___x_2710_);
lean_ctor_set(v___x_2481_, 0, v_pos_2707_);
v___x_2712_ = v___x_2481_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_pos_2707_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
else
{
uint8_t v___x_2714_; uint8_t v_got_2715_; uint8_t v___x_2716_; 
v___x_2714_ = 59;
v_got_2715_ = lean_byte_array_fget(v_array_2489_, v_idx_2490_);
v___x_2716_ = lean_uint8_dec_eq(v_got_2715_, v___x_2714_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
lean_dec(v_idx_2490_);
lean_dec_ref(v_array_2489_);
lean_del_object(v___x_2487_);
v___x_2717_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7));
if (v_isShared_2482_ == 0)
{
lean_ctor_set_tag(v___x_2481_, 1);
lean_ctor_set(v___x_2481_, 1, v___x_2717_);
lean_ctor_set(v___x_2481_, 0, v_pos_2707_);
v___x_2719_ = v___x_2481_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_pos_2707_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
lean_dec_ref(v_pos_2707_);
v___x_2721_ = lean_unsigned_to_nat(1u);
v___x_2722_ = lean_nat_add(v_idx_2490_, v___x_2721_);
lean_dec(v_idx_2490_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v___x_2722_);
lean_ctor_set(v___x_2481_, 0, v_array_2489_);
v___x_2724_ = v___x_2481_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_array_2489_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; lean_object* v_snd_2726_; lean_object* v_snd_2727_; uint8_t v___x_2728_; 
v___x_2725_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2476_, v_maxSpaceSequence_2473_, v___x_2477_, v___x_2724_);
v_snd_2726_ = lean_ctor_get(v___x_2725_, 1);
lean_inc(v_snd_2726_);
lean_dec_ref(v___x_2725_);
v_snd_2727_ = lean_ctor_get(v_snd_2726_, 1);
v___x_2728_ = lean_unbox(v_snd_2727_);
if (v___x_2728_ == 0)
{
lean_object* v_fst_2729_; lean_object* v_array_2730_; lean_object* v_idx_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v_fst_2729_ = lean_ctor_get(v_snd_2726_, 0);
lean_inc(v_fst_2729_);
lean_dec(v_snd_2726_);
v_array_2730_ = lean_ctor_get(v_fst_2729_, 0);
v_idx_2731_ = lean_ctor_get(v_fst_2729_, 1);
v___x_2732_ = lean_byte_array_size(v_array_2730_);
v___x_2733_ = lean_nat_dec_lt(v_idx_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
v_pos_2674_ = v_fst_2729_;
goto v___jp_2673_;
}
else
{
uint8_t v___x_2734_; uint32_t v___x_2735_; uint32_t v___x_2736_; uint8_t v___x_2737_; 
v___x_2734_ = lean_byte_array_fget(v_array_2730_, v_idx_2731_);
v___x_2735_ = lean_uint8_to_uint32(v___x_2734_);
v___x_2736_ = 32;
v___x_2737_ = lean_uint32_dec_eq(v___x_2735_, v___x_2736_);
if (v___x_2737_ == 0)
{
uint32_t v___x_2738_; uint8_t v___x_2739_; 
v___x_2738_ = 9;
v___x_2739_ = lean_uint32_dec_eq(v___x_2735_, v___x_2738_);
if (v___x_2739_ == 0)
{
v_pos_2674_ = v_fst_2729_;
goto v___jp_2673_;
}
else
{
lean_del_object(v___x_2487_);
v_pos_2411_ = v_fst_2729_;
goto v___jp_2410_;
}
}
else
{
lean_del_object(v___x_2487_);
v_pos_2411_ = v_fst_2729_;
goto v___jp_2410_;
}
}
}
else
{
lean_object* v_fst_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2748_; 
lean_del_object(v___x_2487_);
v_fst_2740_ = lean_ctor_get(v_snd_2726_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_snd_2726_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v_snd_2726_, 1);
lean_dec(v_unused_2749_);
v___x_2742_ = v_snd_2726_;
v_isShared_2743_ = v_isSharedCheck_2748_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_fst_2740_);
lean_dec(v_snd_2726_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2748_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2744_ = lean_box(0);
if (v_isShared_2743_ == 0)
{
lean_ctor_set_tag(v___x_2742_, 1);
lean_ctor_set(v___x_2742_, 1, v___x_2744_);
v___x_2746_ = v___x_2742_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_fst_2740_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
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
lean_object* v_fst_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2769_; 
lean_del_object(v___x_2481_);
v_fst_2761_ = lean_ctor_get(v_snd_2479_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_snd_2479_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v_snd_2479_, 1);
lean_dec(v_unused_2770_);
v___x_2763_ = v_snd_2479_;
v_isShared_2764_ = v_isSharedCheck_2769_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_fst_2761_);
lean_dec(v_snd_2479_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2769_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2765_ = lean_box(0);
if (v_isShared_2764_ == 0)
{
lean_ctor_set_tag(v___x_2763_, 1);
lean_ctor_set(v___x_2763_, 1, v___x_2765_);
v___x_2767_ = v___x_2763_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_fst_2761_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2773_, v_a_2774_);
lean_dec_ref(v_limits_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2778_; 
lean_inc_ref(v___y_2777_);
v___x_2778_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_pos_2779_; lean_object* v_res_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v___y_2777_);
v_pos_2779_ = lean_ctor_get(v___x_2778_, 0);
v_res_2780_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2782_ = v___x_2778_;
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_res_2780_);
lean_inc(v_pos_2779_);
lean_dec(v___x_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_res_2780_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 1, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_pos_2779_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_object* v_err_2789_; 
v_err_2789_ = lean_ctor_get(v___x_2778_, 1);
if (lean_obj_tag(v_err_2789_) == 0)
{
lean_object* v_pos_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_inc(v_err_2789_);
lean_dec_ref(v___y_2777_);
v_pos_2790_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v___x_2778_, 1);
lean_dec(v_unused_2798_);
v___x_2792_ = v___x_2778_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_pos_2790_);
lean_dec(v___x_2778_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_pos_2790_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_err_2789_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
else
{
lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2806_; 
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; lean_object* v_unused_2808_; 
v_unused_2807_ = lean_ctor_get(v___x_2778_, 1);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v___x_2778_, 0);
lean_dec(v_unused_2808_);
v___x_2800_ = v___x_2778_;
v_isShared_2801_ = v_isSharedCheck_2806_;
goto v_resetjp_2799_;
}
else
{
lean_dec(v___x_2778_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2806_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = lean_box(0);
if (v_isShared_2801_ == 0)
{
lean_ctor_set_tag(v___x_2800_, 0);
lean_ctor_set(v___x_2800_, 1, v___x_2802_);
lean_ctor_set(v___x_2800_, 0, v___y_2777_);
v___x_2804_ = v___x_2800_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___y_2777_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_2809_, v___y_2810_);
lean_dec_ref(v_limits_2809_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_2813_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_pos_2815_; lean_object* v_res_2816_; lean_object* v_maxChunkExtensions_2817_; lean_object* v___f_2818_; lean_object* v___x_2819_; 
v_pos_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_pos_2815_);
v_res_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_res_2816_);
lean_dec_ref_known(v___x_2814_, 2);
v_maxChunkExtensions_2817_ = lean_ctor_get(v_limits_2812_, 10);
lean_inc(v_maxChunkExtensions_2817_);
v___f_2818_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2818_, 0, v_limits_2812_);
v___x_2819_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_2818_, v_maxChunkExtensions_2817_, v_pos_2815_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_pos_2820_; lean_object* v_res_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_pos_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_pos_2820_);
v_res_2821_ = lean_ctor_get(v___x_2819_, 1);
lean_inc(v_res_2821_);
lean_dec_ref_known(v___x_2819_, 2);
v___x_2822_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2823_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2822_, v_pos_2820_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_pos_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2832_; 
v_pos_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v___x_2823_, 1);
lean_dec(v_unused_2833_);
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2832_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_pos_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2832_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2828_, 0, v_res_2816_);
lean_ctor_set(v___x_2828_, 1, v_res_2821_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 1, v___x_2828_);
v___x_2830_ = v___x_2826_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_pos_2824_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
lean_object* v_pos_2834_; lean_object* v_err_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_res_2821_);
lean_dec(v_res_2816_);
v_pos_2834_ = lean_ctor_get(v___x_2823_, 0);
v_err_2835_ = lean_ctor_get(v___x_2823_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2823_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_err_2835_);
lean_inc(v_pos_2834_);
lean_dec(v___x_2823_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_pos_2834_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_err_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_pos_2843_; lean_object* v_err_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v_res_2816_);
v_pos_2843_ = lean_ctor_get(v___x_2819_, 0);
v_err_2844_ = lean_ctor_get(v___x_2819_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2819_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_err_2844_);
lean_inc(v_pos_2843_);
lean_dec(v___x_2819_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_pos_2843_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_err_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
else
{
lean_object* v_pos_2852_; lean_object* v_err_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v_limits_2812_);
v_pos_2852_ = lean_ctor_get(v___x_2814_, 0);
v_err_2853_ = lean_ctor_get(v___x_2814_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2814_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_err_2853_);
lean_inc(v_pos_2852_);
lean_dec(v___x_2814_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_pos_2852_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_err_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object* v_x_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = lean_obj_tag_nat(v_x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object* v_x_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(v_x_2863_);
lean_dec_ref(v_x_2863_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_2865_, lean_object* v_k_2866_){
_start:
{
if (lean_obj_tag(v_t_2865_) == 0)
{
lean_object* v_data_2867_; lean_object* v___x_2868_; 
v_data_2867_ = lean_ctor_get(v_t_2865_, 0);
lean_inc_ref(v_data_2867_);
lean_dec_ref_known(v_t_2865_, 1);
v___x_2868_ = lean_apply_1(v_k_2866_, v_data_2867_);
return v___x_2868_;
}
else
{
lean_object* v_data_2869_; lean_object* v_remaining_2870_; lean_object* v___x_2871_; 
v_data_2869_ = lean_ctor_get(v_t_2865_, 0);
lean_inc_ref(v_data_2869_);
v_remaining_2870_ = lean_ctor_get(v_t_2865_, 1);
lean_inc(v_remaining_2870_);
lean_dec_ref_known(v_t_2865_, 2);
v___x_2871_ = lean_apply_2(v_k_2866_, v_data_2869_, v_remaining_2870_);
return v___x_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_2872_, lean_object* v_ctorIdx_2873_, lean_object* v_t_2874_, lean_object* v_h_2875_, lean_object* v_k_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2874_, v_k_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_2878_, lean_object* v_ctorIdx_2879_, lean_object* v_t_2880_, lean_object* v_h_2881_, lean_object* v_k_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_2878_, v_ctorIdx_2879_, v_t_2880_, v_h_2881_, v_k_2882_);
lean_dec(v_ctorIdx_2879_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_2884_, lean_object* v_complete_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2884_, v_complete_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_2887_, lean_object* v_t_2888_, lean_object* v_h_2889_, lean_object* v_complete_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2888_, v_complete_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_2892_, lean_object* v_incomplete_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2892_, v_incomplete_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_2895_, lean_object* v_t_2896_, lean_object* v_h_2897_, lean_object* v_incomplete_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2896_, v_incomplete_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_res_2903_; lean_object* v_pos_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2944_; 
v_res_2903_ = lean_ctor_get(v___x_2902_, 1);
v_pos_2904_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2906_ = v___x_2902_;
v_isShared_2907_ = v_isSharedCheck_2944_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_res_2903_);
lean_inc(v_pos_2904_);
lean_dec(v___x_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2944_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_fst_2908_; lean_object* v_snd_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2943_; 
v_fst_2908_ = lean_ctor_get(v_res_2903_, 0);
v_snd_2909_ = lean_ctor_get(v_res_2903_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_res_2903_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2911_ = v_res_2903_;
v_isShared_2912_ = v_isSharedCheck_2943_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_snd_2909_);
lean_inc(v_fst_2908_);
lean_dec(v_res_2903_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2943_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = lean_unsigned_to_nat(0u);
v___x_2914_ = lean_nat_dec_eq(v_fst_2908_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
lean_del_object(v___x_2906_);
v___x_2915_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_2908_, v_pos_2904_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_pos_2916_; lean_object* v_res_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2929_; 
v_pos_2916_ = lean_ctor_get(v___x_2915_, 0);
v_res_2917_ = lean_ctor_get(v___x_2915_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2919_ = v___x_2915_;
v_isShared_2920_ = v_isSharedCheck_2929_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_res_2917_);
lean_inc(v_pos_2916_);
lean_dec(v___x_2915_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2929_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v_res_2917_);
lean_ctor_set(v___x_2911_, 0, v_snd_2909_);
v___x_2922_ = v___x_2911_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_snd_2909_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_res_2917_);
v___x_2922_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v_fst_2908_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v___x_2924_);
v___x_2926_ = v___x_2919_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_pos_2916_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_pos_2930_; lean_object* v_err_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_del_object(v___x_2911_);
lean_dec(v_snd_2909_);
lean_dec(v_fst_2908_);
v_pos_2930_ = lean_ctor_get(v___x_2915_, 0);
v_err_2931_ = lean_ctor_get(v___x_2915_, 1);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2915_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_err_2931_);
lean_inc(v_pos_2930_);
lean_dec(v___x_2915_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_pos_2930_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_err_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
lean_del_object(v___x_2911_);
lean_dec(v_snd_2909_);
lean_dec(v_fst_2908_);
v___x_2939_ = lean_box(0);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 1, v___x_2939_);
v___x_2941_ = v___x_2906_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_pos_2904_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
else
{
lean_object* v_pos_2945_; lean_object* v_err_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
v_pos_2945_ = lean_ctor_get(v___x_2902_, 0);
v_err_2946_ = lean_ctor_get(v___x_2902_, 1);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2902_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_err_2946_);
lean_inc(v_pos_2945_);
lean_dec(v___x_2902_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_pos_2945_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_err_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_2954_, lean_object* v_it_2955_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = l_ByteArray_Iterator_remainingBytes(v_it_2955_);
v___x_2957_ = lean_unsigned_to_nat(0u);
v___x_2958_ = lean_nat_dec_eq(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_nat_dec_lt(v___x_2956_, v_size_2954_);
if (v___x_2959_ == 0)
{
lean_object* v_array_2960_; lean_object* v_idx_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v___x_2956_);
v_array_2960_ = lean_ctor_get(v_it_2955_, 0);
v_idx_2961_ = lean_ctor_get(v_it_2955_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_it_2955_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2963_ = v_it_2955_;
v_isShared_2964_ = v_isSharedCheck_2980_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_idx_2961_);
lean_inc(v_array_2960_);
lean_dec(v_it_2955_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2980_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = lean_nat_add(v_idx_2961_, v_size_2954_);
lean_inc(v___x_2965_);
lean_inc_ref(v_array_2960_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_array_2960_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v_lower_2969_; lean_object* v_upper_2970_; lean_object* v___x_2974_; lean_object* v___y_2976_; uint8_t v___x_2978_; 
v___x_2974_ = lean_byte_array_size(v_array_2960_);
v___x_2978_ = lean_nat_dec_le(v_idx_2961_, v___x_2957_);
if (v___x_2978_ == 0)
{
v___y_2976_ = v_idx_2961_;
goto v___jp_2975_;
}
else
{
lean_dec(v_idx_2961_);
v___y_2976_ = v___x_2957_;
goto v___jp_2975_;
}
v___jp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = l_ByteArray_toByteSlice(v_array_2960_, v_lower_2969_, v_upper_2970_);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2967_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
return v___x_2973_;
}
v___jp_2975_:
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_nat_dec_le(v___x_2965_, v___x_2974_);
if (v___x_2977_ == 0)
{
lean_dec(v___x_2965_);
v_lower_2969_ = v___y_2976_;
v_upper_2970_ = v___x_2974_;
goto v___jp_2968_;
}
else
{
v_lower_2969_ = v___y_2976_;
v_upper_2970_ = v___x_2965_;
goto v___jp_2968_;
}
}
}
}
}
else
{
lean_object* v_array_2981_; lean_object* v_idx_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3002_; 
v_array_2981_ = lean_ctor_get(v_it_2955_, 0);
v_idx_2982_ = lean_ctor_get(v_it_2955_, 1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_it_2955_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2984_ = v_it_2955_;
v_isShared_2985_ = v_isSharedCheck_3002_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_idx_2982_);
lean_inc(v_array_2981_);
lean_dec(v_it_2955_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3002_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2986_ = lean_nat_add(v_idx_2982_, v___x_2956_);
lean_inc(v___x_2986_);
lean_inc_ref(v_array_2981_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v___x_2986_);
v___x_2988_ = v___x_2984_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_array_2981_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v___x_2986_);
v___x_2988_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v_lower_2990_; lean_object* v_upper_2991_; lean_object* v___x_2996_; lean_object* v___y_2998_; uint8_t v___x_3000_; 
v___x_2996_ = lean_byte_array_size(v_array_2981_);
v___x_3000_ = lean_nat_dec_le(v_idx_2982_, v___x_2957_);
if (v___x_3000_ == 0)
{
v___y_2998_ = v_idx_2982_;
goto v___jp_2997_;
}
else
{
lean_dec(v_idx_2982_);
v___y_2998_ = v___x_2957_;
goto v___jp_2997_;
}
v___jp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2992_ = l_ByteArray_toByteSlice(v_array_2981_, v_lower_2990_, v_upper_2991_);
v___x_2993_ = lean_nat_sub(v_size_2954_, v___x_2956_);
lean_dec(v___x_2956_);
v___x_2994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2992_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2988_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
return v___x_2995_;
}
v___jp_2997_:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_nat_dec_le(v___x_2986_, v___x_2996_);
if (v___x_2999_ == 0)
{
lean_dec(v___x_2986_);
v_lower_2990_ = v___y_2998_;
v_upper_2991_ = v___x_2996_;
goto v___jp_2989_;
}
else
{
v_lower_2990_ = v___y_2998_;
v_upper_2991_ = v___x_2986_;
goto v___jp_2989_;
}
}
}
}
}
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v___x_2956_);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v_it_2955_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
return v___x_3004_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3005_, lean_object* v_it_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3005_, v_it_3006_);
lean_dec(v_size_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3008_, v_a_3009_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_res_3011_; 
v_res_3011_ = lean_ctor_get(v___x_3010_, 1);
if (lean_obj_tag(v_res_3011_) == 0)
{
lean_object* v_pos_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_inc_ref(v_res_3011_);
v_pos_3012_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_pos_3012_);
lean_dec_ref_known(v___x_3010_, 2);
v___x_3013_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3014_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3013_, v_pos_3012_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_pos_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_pos_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_3014_, 1);
lean_dec(v_unused_3023_);
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_pos_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 1, v_res_3011_);
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_pos_3015_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_res_3011_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_pos_3024_; lean_object* v_err_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref_known(v_res_3011_, 1);
v_pos_3024_ = lean_ctor_get(v___x_3014_, 0);
v_err_3025_ = lean_ctor_get(v___x_3014_, 1);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3014_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_err_3025_);
lean_inc(v_pos_3024_);
lean_dec(v___x_3014_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_pos_3024_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_err_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
return v___x_3010_;
}
}
else
{
return v___x_3010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3033_, v_a_3034_);
lean_dec(v_size_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object* v_s_3036_, lean_object* v_p_3037_){
_start:
{
lean_object* v___y_3039_; lean_object* v___y_3040_; uint32_t v___y_3044_; lean_object* v___x_3056_; uint8_t v_decide_3057_; 
v___x_3056_ = lean_string_utf8_byte_size(v_s_3036_);
v_decide_3057_ = lean_nat_dec_eq(v_p_3037_, v___x_3056_);
if (v_decide_3057_ == 0)
{
uint32_t v___x_3058_; uint32_t v___x_3059_; uint8_t v___x_3060_; 
v___x_3058_ = lean_string_utf8_get_fast(v_s_3036_, v_p_3037_);
v___x_3059_ = 65;
v___x_3060_ = lean_uint32_dec_le(v___x_3059_, v___x_3058_);
if (v___x_3060_ == 0)
{
v___y_3044_ = v___x_3058_;
goto v___jp_3043_;
}
else
{
uint32_t v___x_3061_; uint8_t v___x_3062_; 
v___x_3061_ = 90;
v___x_3062_ = lean_uint32_dec_le(v___x_3058_, v___x_3061_);
if (v___x_3062_ == 0)
{
v___y_3044_ = v___x_3058_;
goto v___jp_3043_;
}
else
{
uint32_t v___x_3063_; uint32_t v___x_3064_; 
v___x_3063_ = 32;
v___x_3064_ = lean_uint32_add(v___x_3058_, v___x_3063_);
v___y_3044_ = v___x_3064_;
goto v___jp_3043_;
}
}
}
else
{
lean_dec(v_p_3037_);
return v_s_3036_;
}
v___jp_3038_:
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_nat_add(v_p_3037_, v___y_3040_);
lean_dec(v_p_3037_);
v_s_3036_ = v___y_3039_;
v_p_3037_ = v___x_3041_;
goto _start;
}
v___jp_3043_:
{
lean_object* v___x_3045_; uint32_t v___x_3046_; uint8_t v___x_3047_; 
lean_inc(v_p_3037_);
v___x_3045_ = lean_string_utf8_set(v_s_3036_, v_p_3037_, v___y_3044_);
v___x_3046_ = 127;
v___x_3047_ = lean_uint32_dec_le(v___y_3044_, v___x_3046_);
if (v___x_3047_ == 0)
{
uint32_t v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = 2047;
v___x_3049_ = lean_uint32_dec_le(v___y_3044_, v___x_3048_);
if (v___x_3049_ == 0)
{
uint32_t v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = 65535;
v___x_3051_ = lean_uint32_dec_le(v___y_3044_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_unsigned_to_nat(4u);
v___y_3039_ = v___x_3045_;
v___y_3040_ = v___x_3052_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_unsigned_to_nat(3u);
v___y_3039_ = v___x_3045_;
v___y_3040_ = v___x_3053_;
goto v___jp_3038_;
}
}
else
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_unsigned_to_nat(2u);
v___y_3039_ = v___x_3045_;
v___y_3040_ = v___x_3054_;
goto v___jp_3038_;
}
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_unsigned_to_nat(1u);
v___y_3039_ = v___x_3045_;
v___y_3040_ = v___x_3055_;
goto v___jp_3038_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3077_){
_start:
{
lean_object* v___x_3078_; lean_object* v_n_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3078_ = lean_unsigned_to_nat(0u);
v_n_3079_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(v_name_3077_, v___x_3078_);
v___x_3080_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3081_ = lean_string_dec_eq(v_n_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3083_ = lean_string_dec_eq(v_n_3079_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3085_ = lean_string_dec_eq(v_n_3079_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3086_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3087_ = lean_string_dec_eq(v_n_3079_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3088_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3089_ = lean_string_dec_eq(v_n_3079_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5));
v___x_3091_ = lean_string_dec_eq(v_n_3079_, v___x_3090_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3092_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6));
v___x_3093_ = lean_string_dec_eq(v_n_3079_, v___x_3092_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7));
v___x_3095_ = lean_string_dec_eq(v_n_3079_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8));
v___x_3097_ = lean_string_dec_eq(v_n_3079_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9));
v___x_3099_ = lean_string_dec_eq(v_n_3079_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3100_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10));
v___x_3101_ = lean_string_dec_eq(v_n_3079_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11));
v___x_3103_ = lean_string_dec_eq(v_n_3079_, v___x_3102_);
lean_dec_ref(v_n_3079_);
return v___x_3103_;
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3101_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3099_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3097_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3095_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3093_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3091_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3089_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3087_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3085_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3083_;
}
}
else
{
lean_dec_ref(v_n_3079_);
return v___x_3081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3104_){
_start:
{
uint8_t v_res_3105_; lean_object* v_r_3106_; 
v_res_3105_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3104_);
v_r_3106_ = lean_box(v_res_3105_);
return v_r_3106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3108_, v_a_3109_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_res_3111_; 
v_res_3111_ = lean_ctor_get(v___x_3110_, 1);
lean_inc(v_res_3111_);
if (lean_obj_tag(v_res_3111_) == 1)
{
lean_object* v_val_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3133_; 
v_val_3112_ = lean_ctor_get(v_res_3111_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_res_3111_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3114_ = v_res_3111_;
v_isShared_3115_ = v_isSharedCheck_3133_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_val_3112_);
lean_dec(v_res_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3133_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v_pos_3116_; lean_object* v_fst_3117_; uint8_t v___x_3118_; 
v_pos_3116_ = lean_ctor_get(v___x_3110_, 0);
v_fst_3117_ = lean_ctor_get(v_val_3112_, 0);
lean_inc_n(v_fst_3117_, 2);
lean_dec(v_val_3112_);
v___x_3118_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3117_);
if (v___x_3118_ == 0)
{
lean_dec(v_fst_3117_);
lean_del_object(v___x_3114_);
return v___x_3110_;
}
else
{
lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3130_; 
lean_inc(v_pos_3116_);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; lean_object* v_unused_3132_; 
v_unused_3131_ = lean_ctor_get(v___x_3110_, 1);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v___x_3110_, 0);
lean_dec(v_unused_3132_);
v___x_3120_ = v___x_3110_;
v_isShared_3121_ = v_isSharedCheck_3130_;
goto v_resetjp_3119_;
}
else
{
lean_dec(v___x_3110_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3130_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3122_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3123_ = lean_string_append(v___x_3122_, v_fst_3117_);
lean_dec(v_fst_3117_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3123_);
v___x_3125_ = v___x_3114_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3127_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set_tag(v___x_3120_, 1);
lean_ctor_set(v___x_3120_, 1, v___x_3125_);
v___x_3127_ = v___x_3120_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_pos_3116_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3111_);
return v___x_3110_;
}
}
else
{
return v___x_3110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3134_, v_a_3135_);
lean_dec_ref(v_limits_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_maxTrailerHeaders_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_maxTrailerHeaders_3139_ = lean_ctor_get(v_limits_3137_, 17);
lean_inc(v_maxTrailerHeaders_3139_);
v___x_3140_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3140_, 0, v_limits_3137_);
v___x_3141_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3140_, v_maxTrailerHeaders_3139_, v_a_3138_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_pos_3142_; lean_object* v_res_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v_pos_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_pos_3142_);
v_res_3143_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_res_3143_);
lean_dec_ref_known(v___x_3141_, 2);
v___x_3144_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3145_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3144_, v_pos_3142_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_pos_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v_pos_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; 
v_unused_3154_ = lean_ctor_get(v___x_3145_, 1);
lean_dec(v_unused_3154_);
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_pos_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v_res_3143_);
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_pos_3146_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_res_3143_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
else
{
lean_object* v_pos_3155_; lean_object* v_err_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_res_3143_);
v_pos_3155_ = lean_ctor_get(v___x_3145_, 0);
v_err_3156_ = lean_ctor_get(v___x_3145_, 1);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3145_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_err_3156_);
lean_inc(v_pos_3155_);
lean_dec(v___x_3145_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_pos_3155_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_err_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
return v___x_3141_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3164_){
_start:
{
uint32_t v___x_3165_; uint32_t v___x_3171_; uint8_t v___x_3172_; 
v___x_3165_ = lean_uint8_to_uint32(v_c_3164_);
v___x_3171_ = 33;
v___x_3172_ = lean_uint32_dec_le(v___x_3171_, v___x_3165_);
if (v___x_3172_ == 0)
{
goto v___jp_3166_;
}
else
{
uint32_t v___x_3173_; uint8_t v___x_3174_; 
v___x_3173_ = 126;
v___x_3174_ = lean_uint32_dec_le(v___x_3165_, v___x_3173_);
if (v___x_3174_ == 0)
{
goto v___jp_3166_;
}
else
{
return v___x_3174_;
}
}
v___jp_3166_:
{
uint32_t v___x_3167_; uint8_t v___x_3168_; 
v___x_3167_ = 32;
v___x_3168_ = lean_uint32_dec_eq(v___x_3165_, v___x_3167_);
if (v___x_3168_ == 0)
{
uint32_t v___x_3169_; uint8_t v___x_3170_; 
v___x_3169_ = 9;
v___x_3170_ = lean_uint32_dec_eq(v___x_3165_, v___x_3169_);
return v___x_3170_;
}
else
{
return v___x_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3175_){
_start:
{
uint8_t v_c_boxed_3176_; uint8_t v_res_3177_; lean_object* v_r_3178_; 
v_c_boxed_3176_ = lean_unbox(v_c_3175_);
v_res_3177_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3176_);
v_r_3178_ = lean_box(v_res_3177_);
return v_r_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v_maxReasonPhraseLength_3181_; lean_object* v___f_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v_snd_3185_; lean_object* v_snd_3186_; uint8_t v___x_3187_; 
v_maxReasonPhraseLength_3181_ = lean_ctor_get(v_limits_3179_, 16);
v___f_3182_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_3183_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3180_);
v___x_3184_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3182_, v_maxReasonPhraseLength_3181_, v___x_3183_, v_a_3180_);
v_snd_3185_ = lean_ctor_get(v___x_3184_, 1);
lean_inc(v_snd_3185_);
v_snd_3186_ = lean_ctor_get(v_snd_3185_, 1);
v___x_3187_ = lean_unbox(v_snd_3186_);
if (v___x_3187_ == 0)
{
lean_object* v_fst_3188_; lean_object* v_fst_3189_; lean_object* v_array_3190_; lean_object* v_idx_3191_; lean_object* v_lower_3193_; lean_object* v_upper_3194_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___y_3206_; uint8_t v___x_3208_; 
v_fst_3188_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_fst_3188_);
lean_dec_ref(v___x_3184_);
v_fst_3189_ = lean_ctor_get(v_snd_3185_, 0);
lean_inc(v_fst_3189_);
lean_dec(v_snd_3185_);
v_array_3190_ = lean_ctor_get(v_a_3180_, 0);
lean_inc_ref(v_array_3190_);
v_idx_3191_ = lean_ctor_get(v_a_3180_, 1);
lean_inc(v_idx_3191_);
lean_dec_ref(v_a_3180_);
v___x_3203_ = lean_nat_add(v_idx_3191_, v_fst_3188_);
lean_dec(v_fst_3188_);
v___x_3204_ = lean_byte_array_size(v_array_3190_);
v___x_3208_ = lean_nat_dec_le(v_idx_3191_, v___x_3183_);
if (v___x_3208_ == 0)
{
v___y_3206_ = v_idx_3191_;
goto v___jp_3205_;
}
else
{
lean_dec(v_idx_3191_);
v___y_3206_ = v___x_3183_;
goto v___jp_3205_;
}
v___jp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v___x_3195_ = l_ByteArray_toByteSlice(v_array_3190_, v_lower_3193_, v_upper_3194_);
v___x_3196_ = l_ByteSlice_toByteArray(v___x_3195_);
v___x_3197_ = lean_string_validate_utf8(v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_dec_ref(v___x_3196_);
v___x_3198_ = lean_box(0);
v___x_3199_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3198_, v_fst_3189_);
return v___x_3199_;
}
else
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = lean_string_from_utf8_unchecked(v___x_3196_);
v___x_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
v___x_3202_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3201_, v_fst_3189_);
lean_dec_ref_known(v___x_3201_, 1);
return v___x_3202_;
}
}
v___jp_3205_:
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_nat_dec_le(v___x_3203_, v___x_3204_);
if (v___x_3207_ == 0)
{
lean_dec(v___x_3203_);
v_lower_3193_ = v___y_3206_;
v_upper_3194_ = v___x_3204_;
goto v___jp_3192_;
}
else
{
v_lower_3193_ = v___y_3206_;
v_upper_3194_ = v___x_3203_;
goto v___jp_3192_;
}
}
}
else
{
lean_object* v_fst_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3217_; 
lean_dec_ref(v___x_3184_);
lean_dec_ref(v_a_3180_);
v_fst_3209_ = lean_ctor_get(v_snd_3185_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_snd_3185_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v_snd_3185_, 1);
lean_dec(v_unused_3218_);
v___x_3211_ = v_snd_3185_;
v_isShared_3212_ = v_isSharedCheck_3217_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_fst_3209_);
lean_dec(v_snd_3185_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3217_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3213_ = lean_box(0);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 1);
lean_ctor_set(v___x_3211_, 1, v___x_3213_);
v___x_3215_ = v___x_3211_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_fst_3209_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3219_, v_a_3220_);
lean_dec_ref(v_limits_3219_);
return v_res_3221_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3222_){
_start:
{
if (lean_obj_tag(v_x_3222_) == 0)
{
uint8_t v___x_3223_; 
v___x_3223_ = 1;
return v___x_3223_;
}
else
{
lean_object* v_head_3224_; lean_object* v_tail_3225_; uint32_t v___x_3226_; uint32_t v___x_3227_; uint8_t v___x_3228_; 
v_head_3224_ = lean_ctor_get(v_x_3222_, 0);
v_tail_3225_ = lean_ctor_get(v_x_3222_, 1);
v___x_3226_ = 9;
v___x_3227_ = lean_unbox_uint32(v_head_3224_);
v___x_3228_ = lean_uint32_dec_eq(v___x_3227_, v___x_3226_);
if (v___x_3228_ == 0)
{
uint32_t v___x_3229_; uint32_t v___x_3230_; uint8_t v___x_3231_; 
v___x_3229_ = 32;
v___x_3230_ = lean_unbox_uint32(v_head_3224_);
v___x_3231_ = lean_uint32_dec_eq(v___x_3230_, v___x_3229_);
if (v___x_3231_ == 0)
{
uint32_t v___x_3232_; uint32_t v___x_3233_; uint8_t v___x_3234_; 
v___x_3232_ = 33;
v___x_3233_ = lean_unbox_uint32(v_head_3224_);
v___x_3234_ = lean_uint32_dec_le(v___x_3232_, v___x_3233_);
if (v___x_3234_ == 0)
{
return v___x_3234_;
}
else
{
uint32_t v___x_3235_; uint32_t v___x_3236_; uint8_t v___x_3237_; 
v___x_3235_ = 126;
v___x_3236_ = lean_unbox_uint32(v_head_3224_);
v___x_3237_ = lean_uint32_dec_le(v___x_3236_, v___x_3235_);
if (v___x_3237_ == 0)
{
return v___x_3237_;
}
else
{
v_x_3222_ = v_tail_3225_;
goto _start;
}
}
}
else
{
v_x_3222_ = v_tail_3225_;
goto _start;
}
}
else
{
v_x_3222_ = v_tail_3225_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3241_){
_start:
{
uint8_t v_res_3242_; lean_object* v_r_3243_; 
v_res_3242_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3241_);
lean_dec(v_x_3241_);
v_r_3243_ = lean_box(v_res_3242_);
return v_r_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3247_, lean_object* v_a_3248_){
_start:
{
lean_object* v_array_3252_; lean_object* v_idx_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v_array_3252_ = lean_ctor_get(v_a_3248_, 0);
v_idx_3253_ = lean_ctor_get(v_a_3248_, 1);
v___x_3254_ = lean_byte_array_size(v_array_3252_);
v___x_3255_ = lean_nat_dec_lt(v_idx_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3257_, 0, v_a_3248_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
return v___x_3257_;
}
else
{
uint8_t v_c_3258_; uint8_t v___x_3259_; uint8_t v___x_3260_; 
v_c_3258_ = lean_byte_array_fget(v_array_3252_, v_idx_3253_);
v___x_3259_ = 48;
v___x_3260_ = lean_uint8_dec_le(v___x_3259_, v_c_3258_);
if (v___x_3260_ == 0)
{
goto v___jp_3249_;
}
else
{
uint8_t v___x_3261_; uint8_t v___x_3262_; 
v___x_3261_ = 57;
v___x_3262_ = lean_uint8_dec_le(v_c_3258_, v___x_3261_);
if (v___x_3262_ == 0)
{
goto v___jp_3249_;
}
else
{
lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3366_; 
lean_inc(v_idx_3253_);
lean_inc_ref(v_array_3252_);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_a_3248_);
if (v_isSharedCheck_3366_ == 0)
{
lean_object* v_unused_3367_; lean_object* v_unused_3368_; 
v_unused_3367_ = lean_ctor_get(v_a_3248_, 1);
lean_dec(v_unused_3367_);
v_unused_3368_ = lean_ctor_get(v_a_3248_, 0);
lean_dec(v_unused_3368_);
v___x_3264_ = v_a_3248_;
v_isShared_3265_ = v_isSharedCheck_3366_;
goto v_resetjp_3263_;
}
else
{
lean_dec(v_a_3248_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3366_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v_it_x27_3269_; 
v___x_3266_ = lean_unsigned_to_nat(1u);
v___x_3267_ = lean_nat_add(v_idx_3253_, v___x_3266_);
lean_dec(v_idx_3253_);
lean_inc(v___x_3267_);
lean_inc_ref(v_array_3252_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 1, v___x_3267_);
v_it_x27_3269_ = v___x_3264_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_array_3252_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v___x_3267_);
v_it_x27_3269_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
uint8_t v___x_3273_; 
v___x_3273_ = lean_nat_dec_lt(v___x_3267_, v___x_3254_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v___x_3267_);
lean_dec_ref(v_array_3252_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3275_, 0, v_it_x27_3269_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
return v___x_3275_;
}
else
{
uint8_t v_c_3276_; uint8_t v___x_3277_; 
v_c_3276_ = lean_byte_array_fget(v_array_3252_, v___x_3267_);
v___x_3277_ = lean_uint8_dec_le(v___x_3259_, v_c_3276_);
if (v___x_3277_ == 0)
{
lean_dec(v___x_3267_);
lean_dec_ref(v_array_3252_);
goto v___jp_3270_;
}
else
{
uint8_t v___x_3278_; 
v___x_3278_ = lean_uint8_dec_le(v_c_3276_, v___x_3261_);
if (v___x_3278_ == 0)
{
lean_dec(v___x_3267_);
lean_dec_ref(v_array_3252_);
goto v___jp_3270_;
}
else
{
lean_object* v___x_3279_; lean_object* v_it_x27_3280_; uint8_t v___x_3284_; 
lean_dec_ref(v_it_x27_3269_);
v___x_3279_ = lean_nat_add(v___x_3267_, v___x_3266_);
lean_dec(v___x_3267_);
lean_inc(v___x_3279_);
lean_inc_ref(v_array_3252_);
v_it_x27_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3280_, 0, v_array_3252_);
lean_ctor_set(v_it_x27_3280_, 1, v___x_3279_);
v___x_3284_ = lean_nat_dec_lt(v___x_3279_, v___x_3254_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec(v___x_3279_);
lean_dec_ref(v_array_3252_);
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3286_, 0, v_it_x27_3280_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
return v___x_3286_;
}
else
{
uint8_t v_c_3287_; uint8_t v___x_3288_; 
v_c_3287_ = lean_byte_array_fget(v_array_3252_, v___x_3279_);
v___x_3288_ = lean_uint8_dec_le(v___x_3259_, v_c_3287_);
if (v___x_3288_ == 0)
{
lean_dec(v___x_3279_);
lean_dec_ref(v_array_3252_);
goto v___jp_3281_;
}
else
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_uint8_dec_le(v_c_3287_, v___x_3261_);
if (v___x_3289_ == 0)
{
lean_dec(v___x_3279_);
lean_dec_ref(v_array_3252_);
goto v___jp_3281_;
}
else
{
lean_object* v___x_3290_; lean_object* v_it_x27_3291_; uint8_t v___x_3292_; 
lean_dec_ref_known(v_it_x27_3280_, 2);
v___x_3290_ = lean_nat_add(v___x_3279_, v___x_3266_);
lean_dec(v___x_3279_);
lean_inc(v___x_3290_);
lean_inc_ref(v_array_3252_);
v_it_x27_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3291_, 0, v_array_3252_);
lean_ctor_set(v_it_x27_3291_, 1, v___x_3290_);
v___x_3292_ = lean_nat_dec_lt(v___x_3290_, v___x_3254_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec(v___x_3290_);
lean_dec_ref(v_array_3252_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3294_, 0, v_it_x27_3291_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
return v___x_3294_;
}
else
{
uint8_t v___x_3295_; uint8_t v_got_3296_; uint8_t v___x_3297_; 
v___x_3295_ = 32;
v_got_3296_ = lean_byte_array_fget(v_array_3252_, v___x_3290_);
v___x_3297_ = lean_uint8_dec_eq(v_got_3296_, v___x_3295_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v___x_3290_);
lean_dec_ref(v_array_3252_);
v___x_3298_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3299_, 0, v_it_x27_3291_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec_ref_known(v_it_x27_3291_, 2);
v___x_3300_ = lean_nat_add(v___x_3290_, v___x_3266_);
lean_dec(v___x_3290_);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v_array_3252_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3247_, v___x_3301_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_pos_3303_; lean_object* v_res_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3355_; 
v_pos_3303_ = lean_ctor_get(v___x_3302_, 0);
v_res_3304_ = lean_ctor_get(v___x_3302_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3306_ = v___x_3302_;
v_isShared_3307_ = v_isSharedCheck_3355_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_res_3304_);
lean_inc(v_pos_3303_);
lean_dec(v___x_3302_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3355_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3309_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3308_, v_pos_3303_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_pos_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3344_; 
v_pos_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; 
v_unused_3345_ = lean_ctor_get(v___x_3309_, 1);
lean_dec(v_unused_3345_);
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3344_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_pos_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3344_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
lean_inc(v_res_3304_);
v___x_3319_ = l_String_toListImpl(v_res_3304_);
v___x_3320_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3319_);
lean_dec(v___x_3319_);
if (v___x_3320_ == 0)
{
lean_del_object(v___x_3306_);
lean_dec(v_res_3304_);
goto v___jp_3314_;
}
else
{
lean_object* v___x_3321_; uint32_t v___x_3322_; uint32_t v___x_3323_; uint32_t v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint16_t v___x_3338_; lean_object* v___x_3339_; 
v___x_3321_ = lean_unsigned_to_nat(48u);
v___x_3322_ = lean_uint8_to_uint32(v_c_3258_);
v___x_3323_ = lean_uint8_to_uint32(v_c_3276_);
v___x_3324_ = lean_uint8_to_uint32(v_c_3287_);
v___x_3325_ = lean_uint32_to_nat(v___x_3322_);
v___x_3326_ = lean_nat_sub(v___x_3325_, v___x_3321_);
lean_dec(v___x_3325_);
v___x_3327_ = lean_unsigned_to_nat(100u);
v___x_3328_ = lean_nat_mul(v___x_3326_, v___x_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_uint32_to_nat(v___x_3323_);
v___x_3330_ = lean_nat_sub(v___x_3329_, v___x_3321_);
lean_dec(v___x_3329_);
v___x_3331_ = lean_unsigned_to_nat(10u);
v___x_3332_ = lean_nat_mul(v___x_3330_, v___x_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_nat_add(v___x_3328_, v___x_3332_);
lean_dec(v___x_3332_);
lean_dec(v___x_3328_);
v___x_3334_ = lean_uint32_to_nat(v___x_3324_);
v___x_3335_ = lean_nat_sub(v___x_3334_, v___x_3321_);
lean_dec(v___x_3334_);
v___x_3336_ = lean_nat_add(v___x_3333_, v___x_3335_);
lean_dec(v___x_3335_);
lean_dec(v___x_3333_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_res_3304_);
v___x_3338_ = lean_uint16_of_nat(v___x_3336_);
lean_dec(v___x_3336_);
v___x_3339_ = l_Std_Http_Status_ofCode(v___x_3337_, v___x_3338_);
if (lean_obj_tag(v___x_3339_) == 1)
{
lean_object* v_val_3340_; lean_object* v___x_3342_; 
lean_del_object(v___x_3312_);
v_val_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___x_3339_, 1);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 1, v_val_3340_);
lean_ctor_set(v___x_3306_, 0, v_pos_3310_);
v___x_3342_ = v___x_3306_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_pos_3310_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_val_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
else
{
lean_dec(v___x_3339_);
lean_del_object(v___x_3306_);
goto v___jp_3314_;
}
}
v___jp_3314_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3315_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 1);
lean_ctor_set(v___x_3312_, 1, v___x_3315_);
v___x_3317_ = v___x_3312_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_pos_3310_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_pos_3346_; lean_object* v_err_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_del_object(v___x_3306_);
lean_dec(v_res_3304_);
v_pos_3346_ = lean_ctor_get(v___x_3309_, 0);
v_err_3347_ = lean_ctor_get(v___x_3309_, 1);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3309_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_err_3347_);
lean_inc(v_pos_3346_);
lean_dec(v___x_3309_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_pos_3346_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_err_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
else
{
lean_object* v_pos_3356_; lean_object* v_err_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
v_pos_3356_ = lean_ctor_get(v___x_3302_, 0);
v_err_3357_ = lean_ctor_get(v___x_3302_, 1);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3302_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_err_3357_);
lean_inc(v_pos_3356_);
lean_dec(v___x_3302_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_pos_3356_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_err_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
}
}
}
v___jp_3281_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_it_x27_3280_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
return v___x_3283_;
}
}
}
}
v___jp_3270_:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_it_x27_3269_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
return v___x_3272_;
}
}
}
}
}
}
v___jp_3249_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3251_, 0, v_a_3248_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
return v___x_3251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3369_, v_a_3370_);
lean_dec_ref(v_limits_3369_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_pos_3375_; lean_object* v_res_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3450_; 
v_pos_3375_ = lean_ctor_get(v___x_3374_, 0);
v_res_3376_ = lean_ctor_get(v___x_3374_, 1);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3378_ = v___x_3374_;
v_isShared_3379_ = v_isSharedCheck_3450_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_res_3376_);
lean_inc(v_pos_3375_);
lean_dec(v___x_3374_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3450_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v_array_3380_; lean_object* v_idx_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v_array_3380_ = lean_ctor_get(v_pos_3375_, 0);
v_idx_3381_ = lean_ctor_get(v_pos_3375_, 1);
v___x_3382_ = lean_byte_array_size(v_array_3380_);
v___x_3383_ = lean_nat_dec_lt(v_idx_3381_, v___x_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3386_; 
lean_dec(v_res_3376_);
v___x_3384_ = lean_box(0);
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 1);
lean_ctor_set(v___x_3378_, 1, v___x_3384_);
v___x_3386_ = v___x_3378_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_pos_3375_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
else
{
uint8_t v___x_3388_; uint8_t v_got_3389_; uint8_t v___x_3390_; 
v___x_3388_ = 32;
v_got_3389_ = lean_byte_array_fget(v_array_3380_, v_idx_3381_);
v___x_3390_ = lean_uint8_dec_eq(v_got_3389_, v___x_3388_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; lean_object* v___x_3393_; 
lean_dec(v_res_3376_);
v___x_3391_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 1);
lean_ctor_set(v___x_3378_, 1, v___x_3391_);
v___x_3393_ = v___x_3378_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_pos_3375_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
else
{
lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3447_; 
lean_inc(v_idx_3381_);
lean_inc_ref(v_array_3380_);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_pos_3375_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; lean_object* v_unused_3449_; 
v_unused_3448_ = lean_ctor_get(v_pos_3375_, 1);
lean_dec(v_unused_3448_);
v_unused_3449_ = lean_ctor_get(v_pos_3375_, 0);
lean_dec(v_unused_3449_);
v___x_3396_ = v_pos_3375_;
v_isShared_3397_ = v_isSharedCheck_3447_;
goto v_resetjp_3395_;
}
else
{
lean_dec(v_pos_3375_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3447_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_fst_3398_; lean_object* v_snd_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3446_; 
v_fst_3398_ = lean_ctor_get(v_res_3376_, 0);
v_snd_3399_ = lean_ctor_get(v_res_3376_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_res_3376_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3401_ = v_res_3376_;
v_isShared_3402_ = v_isSharedCheck_3446_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_snd_3399_);
lean_inc(v_fst_3398_);
lean_dec(v_res_3376_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3446_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3403_ = lean_unsigned_to_nat(1u);
v___x_3404_ = lean_nat_add(v_idx_3381_, v___x_3403_);
lean_dec(v_idx_3381_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v___x_3404_);
v___x_3406_ = v___x_3396_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_array_3380_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3407_; 
v___x_3407_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3372_, v___x_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_pos_3408_; lean_object* v_res_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3435_; 
v_pos_3408_ = lean_ctor_get(v___x_3407_, 0);
v_res_3409_ = lean_ctor_get(v___x_3407_, 1);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3411_ = v___x_3407_;
v_isShared_3412_ = v_isSharedCheck_3435_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_res_3409_);
lean_inc(v_pos_3408_);
lean_dec(v___x_3407_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3435_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_nat_dec_eq(v_fst_3398_, v___x_3403_);
lean_dec(v_fst_3398_);
if (v___x_3418_ == 0)
{
lean_del_object(v___x_3401_);
goto v___jp_3419_;
}
else
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_nat_dec_eq(v_snd_3399_, v___x_3403_);
if (v___x_3428_ == 0)
{
lean_del_object(v___x_3401_);
goto v___jp_3419_;
}
else
{
uint8_t v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_del_object(v___x_3411_);
lean_dec(v_snd_3399_);
lean_del_object(v___x_3378_);
v___x_3429_ = 1;
v___x_3430_ = l_Std_Http_Headers_empty;
v___x_3431_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3431_, 0, v_res_3409_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*2, v___x_3429_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3431_);
lean_ctor_set(v___x_3401_, 0, v_pos_3408_);
v___x_3433_ = v___x_3401_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_pos_3408_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
v___jp_3413_:
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3414_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 1);
lean_ctor_set(v___x_3411_, 1, v___x_3414_);
v___x_3416_ = v___x_3411_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_pos_3408_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
v___jp_3419_:
{
if (v___x_3418_ == 0)
{
lean_dec(v_res_3409_);
lean_dec(v_snd_3399_);
lean_del_object(v___x_3378_);
goto v___jp_3413_;
}
else
{
lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3420_ = lean_unsigned_to_nat(0u);
v___x_3421_ = lean_nat_dec_eq(v_snd_3399_, v___x_3420_);
lean_dec(v_snd_3399_);
if (v___x_3421_ == 0)
{
lean_dec(v_res_3409_);
lean_del_object(v___x_3378_);
goto v___jp_3413_;
}
else
{
uint8_t v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
lean_del_object(v___x_3411_);
v___x_3422_ = 0;
v___x_3423_ = l_Std_Http_Headers_empty;
v___x_3424_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3424_, 0, v_res_3409_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
lean_ctor_set_uint8(v___x_3424_, sizeof(void*)*2, v___x_3422_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 1, v___x_3424_);
lean_ctor_set(v___x_3378_, 0, v_pos_3408_);
v___x_3426_ = v___x_3378_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_pos_3408_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3436_; lean_object* v_err_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_del_object(v___x_3401_);
lean_dec(v_snd_3399_);
lean_dec(v_fst_3398_);
lean_del_object(v___x_3378_);
v_pos_3436_ = lean_ctor_get(v___x_3407_, 0);
v_err_3437_ = lean_ctor_get(v___x_3407_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3407_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_err_3437_);
lean_inc(v_pos_3436_);
lean_dec(v___x_3407_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_pos_3436_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_err_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
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
lean_object* v_pos_3451_; lean_object* v_err_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_pos_3451_ = lean_ctor_get(v___x_3374_, 0);
v_err_3452_ = lean_ctor_get(v___x_3374_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3374_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_err_3452_);
lean_inc(v_pos_3451_);
lean_dec(v___x_3374_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_pos_3451_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_err_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_3460_, v_a_3461_);
lean_dec_ref(v_limits_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3464_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_pos_3466_; lean_object* v_res_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3526_; 
v_pos_3466_ = lean_ctor_get(v___x_3465_, 0);
v_res_3467_ = lean_ctor_get(v___x_3465_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3469_ = v___x_3465_;
v_isShared_3470_ = v_isSharedCheck_3526_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_res_3467_);
lean_inc(v_pos_3466_);
lean_dec(v___x_3465_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3526_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v_array_3471_; lean_object* v_idx_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v_array_3471_ = lean_ctor_get(v_pos_3466_, 0);
v_idx_3472_ = lean_ctor_get(v_pos_3466_, 1);
v___x_3473_ = lean_byte_array_size(v_array_3471_);
v___x_3474_ = lean_nat_dec_lt(v_idx_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
lean_dec(v_res_3467_);
v___x_3475_ = lean_box(0);
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 1);
lean_ctor_set(v___x_3469_, 1, v___x_3475_);
v___x_3477_ = v___x_3469_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_pos_3466_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
else
{
uint8_t v___x_3479_; uint8_t v_got_3480_; uint8_t v___x_3481_; 
v___x_3479_ = 32;
v_got_3480_ = lean_byte_array_fget(v_array_3471_, v_idx_3472_);
v___x_3481_ = lean_uint8_dec_eq(v_got_3480_, v___x_3479_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3484_; 
lean_dec(v_res_3467_);
v___x_3482_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 1);
lean_ctor_set(v___x_3469_, 1, v___x_3482_);
v___x_3484_ = v___x_3469_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_pos_3466_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
else
{
lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3523_; 
lean_inc(v_idx_3472_);
lean_inc_ref(v_array_3471_);
lean_del_object(v___x_3469_);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_pos_3466_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; lean_object* v_unused_3525_; 
v_unused_3524_ = lean_ctor_get(v_pos_3466_, 1);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v_pos_3466_, 0);
lean_dec(v_unused_3525_);
v___x_3487_ = v_pos_3466_;
v_isShared_3488_ = v_isSharedCheck_3523_;
goto v_resetjp_3486_;
}
else
{
lean_dec(v_pos_3466_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3523_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v_fst_3489_; lean_object* v_snd_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3522_; 
v_fst_3489_ = lean_ctor_get(v_res_3467_, 0);
v_snd_3490_ = lean_ctor_get(v_res_3467_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_res_3467_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3492_ = v_res_3467_;
v_isShared_3493_ = v_isSharedCheck_3522_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_snd_3490_);
lean_inc(v_fst_3489_);
lean_dec(v_res_3467_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3522_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3494_ = lean_unsigned_to_nat(1u);
v___x_3495_ = lean_nat_add(v_idx_3472_, v___x_3494_);
lean_dec(v_idx_3472_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3495_);
v___x_3497_ = v___x_3487_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_array_3471_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3498_; 
v___x_3498_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3463_, v___x_3497_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_pos_3499_; lean_object* v_res_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3511_; 
v_pos_3499_ = lean_ctor_get(v___x_3498_, 0);
v_res_3500_ = lean_ctor_get(v___x_3498_, 1);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3502_ = v___x_3498_;
v_isShared_3503_ = v_isSharedCheck_3511_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_res_3500_);
lean_inc(v_pos_3499_);
lean_dec(v___x_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3511_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v___x_3506_; 
v___x_3504_ = l_Std_Http_Version_ofNumber_x3f(v_fst_3489_, v_snd_3490_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v___x_3504_);
lean_ctor_set(v___x_3492_, 0, v_res_3500_);
v___x_3506_ = v___x_3492_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_res_3500_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3508_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v___x_3506_);
v___x_3508_ = v___x_3502_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_pos_3499_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_pos_3512_; lean_object* v_err_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec(v_fst_3489_);
v_pos_3512_ = lean_ctor_get(v___x_3498_, 0);
v_err_3513_ = lean_ctor_get(v___x_3498_, 1);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3498_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_err_3513_);
lean_inc(v_pos_3512_);
lean_dec(v___x_3498_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_pos_3512_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_err_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
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
lean_object* v_pos_3527_; lean_object* v_err_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
v_pos_3527_ = lean_ctor_get(v___x_3465_, 0);
v_err_3528_ = lean_ctor_get(v___x_3465_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3465_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_err_3528_);
lean_inc(v_pos_3527_);
lean_dec(v___x_3465_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_pos_3527_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_err_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_3536_, v_a_3537_);
lean_dec_ref(v_limits_3536_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object* v_limits_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_maxTrailerHeaders_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v_maxTrailerHeaders_3541_ = lean_ctor_get(v_limits_3539_, 17);
lean_inc(v_maxTrailerHeaders_3541_);
v___x_3542_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3542_, 0, v_limits_3539_);
v___x_3543_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3542_, v_maxTrailerHeaders_3541_, v_a_3540_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_pos_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v_pos_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_pos_3544_);
lean_dec_ref_known(v___x_3543_, 2);
v___x_3545_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3546_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3545_, v_pos_3544_);
return v___x_3546_;
}
else
{
lean_object* v_pos_3547_; lean_object* v_err_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_pos_3547_ = lean_ctor_get(v___x_3543_, 0);
v_err_3548_ = lean_ctor_get(v___x_3543_, 1);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3543_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_err_3548_);
lean_inc(v_pos_3547_);
lean_dec(v___x_3543_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_pos_3547_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_err_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
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
