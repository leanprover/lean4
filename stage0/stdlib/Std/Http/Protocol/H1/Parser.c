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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object* v_parser_52_, lean_object* v_maxCount_53_, lean_object* v_acc_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_pos_57_; lean_object* v_err_58_; lean_object* v___x_73_; 
lean_inc_ref(v_parser_52_);
lean_inc_ref(v_a_55_);
v___x_73_ = lean_apply_1(v_parser_52_, v_a_55_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_res_74_; 
v_res_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_res_74_);
if (lean_obj_tag(v_res_74_) == 0)
{
lean_object* v___x_75_; 
lean_dec_ref_known(v___x_73_, 2);
lean_dec(v_maxCount_53_);
lean_dec_ref(v_parser_52_);
v___x_75_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1));
lean_inc_ref(v_a_55_);
v_pos_57_ = v_a_55_;
v_err_58_ = v___x_75_;
goto v___jp_56_;
}
else
{
lean_object* v_pos_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_102_; 
lean_dec_ref(v_a_55_);
v_pos_76_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v___x_73_, 1);
lean_dec(v_unused_103_);
v___x_78_ = v___x_73_;
v_isShared_79_ = v_isSharedCheck_102_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_pos_76_);
lean_dec(v___x_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_102_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v_val_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
v_val_80_ = lean_ctor_get(v_res_74_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_res_74_);
if (v_isSharedCheck_101_ == 0)
{
v___x_82_ = v_res_74_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_val_80_);
lean_dec(v_res_74_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_array_push(v_acc_54_, v_val_80_);
v___x_85_ = lean_array_get_size(v___x_84_);
v___x_86_ = lean_nat_dec_lt(v_maxCount_53_, v___x_85_);
if (v___x_86_ == 0)
{
lean_del_object(v___x_82_);
lean_del_object(v___x_78_);
v_acc_54_ = v___x_84_;
v_a_55_ = v_pos_76_;
goto _start;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
lean_dec_ref(v___x_84_);
lean_dec_ref(v_parser_52_);
v___x_88_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2));
v___x_89_ = l_Nat_reprFast(v___x_85_);
v___x_90_ = lean_string_append(v___x_88_, v___x_89_);
lean_dec_ref(v___x_89_);
v___x_91_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3));
v___x_92_ = lean_string_append(v___x_90_, v___x_91_);
v___x_93_ = l_Nat_reprFast(v_maxCount_53_);
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
lean_dec_ref(v___x_93_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_94_);
v___x_96_ = v___x_82_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_100_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_98_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 1);
lean_ctor_set(v___x_78_, 1, v___x_96_);
v___x_98_ = v___x_78_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_pos_76_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
}
else
{
lean_object* v_err_104_; 
lean_dec(v_maxCount_53_);
lean_dec_ref(v_parser_52_);
v_err_104_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_err_104_);
lean_dec_ref_known(v___x_73_, 2);
lean_inc_ref(v_a_55_);
v_pos_57_ = v_a_55_;
v_err_58_ = v_err_104_;
goto v___jp_56_;
}
v___jp_56_:
{
lean_object* v_idx_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_71_; 
v_idx_59_ = lean_ctor_get(v_a_55_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_a_55_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v_a_55_, 0);
lean_dec(v_unused_72_);
v___x_61_ = v_a_55_;
v_isShared_62_ = v_isSharedCheck_71_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_idx_59_);
lean_dec(v_a_55_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_71_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_idx_63_; uint8_t v___x_64_; 
v_idx_63_ = lean_ctor_get(v_pos_57_, 1);
v___x_64_ = lean_nat_dec_eq(v_idx_59_, v_idx_63_);
lean_dec(v_idx_59_);
if (v___x_64_ == 0)
{
lean_object* v___x_66_; 
lean_dec_ref(v_acc_54_);
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 1);
lean_ctor_set(v___x_61_, 1, v_err_58_);
lean_ctor_set(v___x_61_, 0, v_pos_57_);
v___x_66_ = v___x_61_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_pos_57_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_err_58_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
else
{
lean_object* v___x_69_; 
lean_dec(v_err_58_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v_acc_54_);
lean_ctor_set(v___x_61_, 0, v_pos_57_);
v___x_69_ = v___x_61_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_pos_57_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_acc_54_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object* v_00_u03b1_105_, lean_object* v_parser_106_, lean_object* v_maxCount_107_, lean_object* v_acc_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_106_, v_maxCount_107_, v_acc_108_, v_a_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object* v_parser_113_, lean_object* v_maxCount_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0));
v___x_117_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_113_, v_maxCount_114_, v___x_116_, v_a_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object* v_00_u03b1_118_, lean_object* v_parser_119_, lean_object* v_maxCount_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v_parser_119_, v_maxCount_120_, v_a_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object* v_x_126_, lean_object* v_a_127_){
_start:
{
if (lean_obj_tag(v_x_126_) == 1)
{
lean_object* v_val_128_; lean_object* v___x_129_; 
v_val_128_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_val_128_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_a_127_);
lean_ctor_set(v___x_129_, 1, v_val_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1));
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v_a_127_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object* v_x_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_132_, v_a_133_);
lean_dec(v_x_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object* v_00_u03b1_135_, lean_object* v_x_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_136_, v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object* v_00_u03b1_139_, lean_object* v_x_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(v_00_u03b1_139_, v_x_140_, v_a_141_);
lean_dec(v_x_140_);
return v_res_142_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t v_c_143_){
_start:
{
uint32_t v___x_144_; uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_144_ = lean_uint8_to_uint32(v_c_143_);
v___x_155_ = 33;
v___x_156_ = lean_uint32_dec_eq(v___x_144_, v___x_155_);
if (v___x_156_ == 0)
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 35;
v___x_158_ = lean_uint32_dec_eq(v___x_144_, v___x_157_);
if (v___x_158_ == 0)
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 36;
v___x_160_ = lean_uint32_dec_eq(v___x_144_, v___x_159_);
if (v___x_160_ == 0)
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 37;
v___x_162_ = lean_uint32_dec_eq(v___x_144_, v___x_161_);
if (v___x_162_ == 0)
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 38;
v___x_164_ = lean_uint32_dec_eq(v___x_144_, v___x_163_);
if (v___x_164_ == 0)
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 39;
v___x_166_ = lean_uint32_dec_eq(v___x_144_, v___x_165_);
if (v___x_166_ == 0)
{
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 42;
v___x_168_ = lean_uint32_dec_eq(v___x_144_, v___x_167_);
if (v___x_168_ == 0)
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 43;
v___x_170_ = lean_uint32_dec_eq(v___x_144_, v___x_169_);
if (v___x_170_ == 0)
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 45;
v___x_172_ = lean_uint32_dec_eq(v___x_144_, v___x_171_);
if (v___x_172_ == 0)
{
uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = 46;
v___x_174_ = lean_uint32_dec_eq(v___x_144_, v___x_173_);
if (v___x_174_ == 0)
{
uint32_t v___x_175_; uint8_t v___x_176_; 
v___x_175_ = 94;
v___x_176_ = lean_uint32_dec_eq(v___x_144_, v___x_175_);
if (v___x_176_ == 0)
{
uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = 95;
v___x_178_ = lean_uint32_dec_eq(v___x_144_, v___x_177_);
if (v___x_178_ == 0)
{
uint32_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = 96;
v___x_180_ = lean_uint32_dec_eq(v___x_144_, v___x_179_);
if (v___x_180_ == 0)
{
uint32_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = 124;
v___x_182_ = lean_uint32_dec_eq(v___x_144_, v___x_181_);
if (v___x_182_ == 0)
{
uint32_t v___x_183_; uint8_t v___x_184_; 
v___x_183_ = 126;
v___x_184_ = lean_uint32_dec_eq(v___x_144_, v___x_183_);
if (v___x_184_ == 0)
{
uint32_t v___x_185_; uint8_t v___x_186_; 
v___x_185_ = 48;
v___x_186_ = lean_uint32_dec_le(v___x_185_, v___x_144_);
if (v___x_186_ == 0)
{
goto v___jp_150_;
}
else
{
uint32_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = 57;
v___x_188_ = lean_uint32_dec_le(v___x_144_, v___x_187_);
if (v___x_188_ == 0)
{
goto v___jp_150_;
}
else
{
return v___x_188_;
}
}
}
else
{
return v___x_184_;
}
}
else
{
return v___x_182_;
}
}
else
{
return v___x_180_;
}
}
else
{
return v___x_178_;
}
}
else
{
return v___x_176_;
}
}
else
{
return v___x_174_;
}
}
else
{
return v___x_172_;
}
}
else
{
return v___x_170_;
}
}
else
{
return v___x_168_;
}
}
else
{
return v___x_166_;
}
}
else
{
return v___x_164_;
}
}
else
{
return v___x_162_;
}
}
else
{
return v___x_160_;
}
}
else
{
return v___x_158_;
}
}
else
{
return v___x_156_;
}
v___jp_145_:
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 97;
v___x_147_ = lean_uint32_dec_le(v___x_146_, v___x_144_);
if (v___x_147_ == 0)
{
return v___x_147_;
}
else
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 122;
v___x_149_ = lean_uint32_dec_le(v___x_144_, v___x_148_);
return v___x_149_;
}
}
v___jp_150_:
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 65;
v___x_152_ = lean_uint32_dec_le(v___x_151_, v___x_144_);
if (v___x_152_ == 0)
{
goto v___jp_145_;
}
else
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 90;
v___x_154_ = lean_uint32_dec_le(v___x_144_, v___x_153_);
if (v___x_154_ == 0)
{
goto v___jp_145_;
}
else
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object* v_c_189_){
_start:
{
uint8_t v_c_boxed_190_; uint8_t v_res_191_; lean_object* v_r_192_; 
v_c_boxed_190_ = lean_unbox(v_c_189_);
v_res_191_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_boxed_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object* v_limit_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_snd_202_; lean_object* v_snd_203_; uint8_t v___x_204_; 
v___f_199_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_200_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_198_);
v___x_201_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_199_, v_limit_197_, v___x_200_, v_a_198_);
v_snd_202_ = lean_ctor_get(v___x_201_, 1);
lean_inc(v_snd_202_);
v_snd_203_ = lean_ctor_get(v_snd_202_, 1);
v___x_204_ = lean_unbox(v_snd_203_);
if (v___x_204_ == 0)
{
lean_object* v_fst_205_; lean_object* v_fst_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_234_; 
v_fst_205_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_fst_205_);
lean_dec_ref(v___x_201_);
v_fst_206_ = lean_ctor_get(v_snd_202_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_snd_202_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v_snd_202_, 1);
lean_dec(v_unused_235_);
v___x_208_ = v_snd_202_;
v_isShared_209_ = v_isSharedCheck_234_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_fst_206_);
lean_dec(v_snd_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_234_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint8_t v___x_210_; 
v___x_210_ = lean_nat_dec_eq(v_fst_205_, v___x_200_);
if (v___x_210_ == 0)
{
lean_object* v_array_211_; lean_object* v_idx_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_229_; 
lean_del_object(v___x_208_);
v_array_211_ = lean_ctor_get(v_a_198_, 0);
v_idx_212_ = lean_ctor_get(v_a_198_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_a_198_);
if (v_isSharedCheck_229_ == 0)
{
v___x_214_ = v_a_198_;
v_isShared_215_ = v_isSharedCheck_229_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_idx_212_);
lean_inc(v_array_211_);
lean_dec(v_a_198_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_229_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_lower_217_; lean_object* v_upper_218_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___y_226_; uint8_t v___x_228_; 
v___x_223_ = lean_nat_add(v_idx_212_, v_fst_205_);
lean_dec(v_fst_205_);
v___x_224_ = lean_byte_array_size(v_array_211_);
v___x_228_ = lean_nat_dec_le(v_idx_212_, v___x_200_);
if (v___x_228_ == 0)
{
v___y_226_ = v_idx_212_;
goto v___jp_225_;
}
else
{
lean_dec(v_idx_212_);
v___y_226_ = v___x_200_;
goto v___jp_225_;
}
v___jp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = l_ByteArray_toByteSlice(v_array_211_, v_lower_217_, v_upper_218_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_219_);
lean_ctor_set(v___x_214_, 0, v_fst_206_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
v___jp_225_:
{
uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_le(v___x_223_, v___x_224_);
if (v___x_227_ == 0)
{
lean_dec(v___x_223_);
v_lower_217_ = v___y_226_;
v_upper_218_ = v___x_224_;
goto v___jp_216_;
}
else
{
v_lower_217_ = v___y_226_;
v_upper_218_ = v___x_223_;
goto v___jp_216_;
}
}
}
}
else
{
lean_object* v___x_230_; lean_object* v___x_232_; 
lean_dec(v_fst_206_);
lean_dec(v_fst_205_);
v___x_230_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 1);
lean_ctor_set(v___x_208_, 1, v___x_230_);
lean_ctor_set(v___x_208_, 0, v_a_198_);
v___x_232_ = v___x_208_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_198_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v_fst_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
lean_dec_ref(v___x_201_);
lean_dec_ref(v_a_198_);
v_fst_236_ = lean_ctor_get(v_snd_202_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_snd_202_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_snd_202_, 1);
lean_dec(v_unused_245_);
v___x_238_ = v_snd_202_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_fst_236_);
lean_dec(v_snd_202_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_box(0);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 1);
lean_ctor_set(v___x_238_, 1, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_fst_236_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object* v_limit_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(v_limit_246_, v_a_247_);
lean_dec(v_limit_246_);
return v_res_248_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0));
v___x_251_ = lean_string_to_utf8(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_254_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_253_, v_a_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object* v_limits_258_, lean_object* v_a_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_array_261_; lean_object* v_idx_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_array_261_ = lean_ctor_get(v___y_260_, 0);
v_idx_262_ = lean_ctor_get(v___y_260_, 1);
v___x_263_ = lean_byte_array_size(v_array_261_);
v___x_264_ = lean_nat_dec_lt(v_idx_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___y_260_);
lean_ctor_set(v___x_265_, 1, v_a_259_);
return v___x_265_;
}
else
{
uint8_t v___x_266_; uint8_t v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_byte_array_fget(v_array_261_, v_idx_262_);
v___x_267_ = 13;
v___x_268_ = lean_uint8_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___y_260_);
lean_ctor_set(v___x_269_, 1, v_a_259_);
return v___x_269_;
}
else
{
lean_object* v_maxLeadingEmptyLines_270_; uint8_t v___x_271_; 
v_maxLeadingEmptyLines_270_ = lean_ctor_get(v_limits_258_, 9);
v___x_271_ = lean_nat_dec_le(v_maxLeadingEmptyLines_270_, v_a_259_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_273_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_272_, v___y_260_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_pos_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_pos_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_pos_274_);
lean_dec_ref_known(v___x_273_, 2);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_a_259_, v___x_275_);
lean_dec(v_a_259_);
v_a_259_ = v___x_276_;
v___y_260_ = v_pos_274_;
goto _start;
}
else
{
lean_object* v_pos_278_; lean_object* v_err_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec(v_a_259_);
v_pos_278_ = lean_ctor_get(v___x_273_, 0);
v_err_279_ = lean_ctor_get(v___x_273_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_273_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_err_279_);
lean_inc(v_pos_278_);
lean_dec(v___x_273_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_pos_278_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_err_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_a_259_);
v___x_287_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1));
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v___y_260_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object* v_limits_289_, lean_object* v_a_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_289_, v_a_290_, v___y_291_);
lean_dec_ref(v_limits_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_count_295_; lean_object* v___x_296_; 
v_count_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_293_, v_count_295_, v_a_294_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_pos_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
v_pos_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_296_, 1);
lean_dec(v_unused_306_);
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_pos_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_box(0);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_pos_297_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v_pos_307_; lean_object* v_err_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_pos_307_ = lean_ctor_get(v___x_296_, 0);
v_err_308_ = lean_ctor_get(v___x_296_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_296_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_err_308_);
lean_inc(v_pos_307_);
lean_dec(v___x_296_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_pos_307_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_err_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object* v_limits_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_316_, v_a_317_);
lean_dec_ref(v_limits_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_319_, lean_object* v_inst_320_, lean_object* v_a_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_319_, v_a_321_, v___y_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_324_, lean_object* v_inst_325_, lean_object* v_a_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_324_, v_inst_325_, v_a_326_, v___y_327_);
lean_dec_ref(v_limits_324_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_332_){
_start:
{
lean_object* v_array_333_; lean_object* v_idx_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_array_333_ = lean_ctor_get(v_a_332_, 0);
v_idx_334_ = lean_ctor_get(v_a_332_, 1);
v___x_335_ = lean_byte_array_size(v_array_333_);
v___x_336_ = lean_nat_dec_lt(v_idx_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v_a_332_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
return v___x_338_;
}
else
{
uint8_t v___x_339_; uint8_t v_got_340_; uint8_t v___x_341_; 
v___x_339_ = 32;
v_got_340_ = lean_byte_array_fget(v_array_333_, v_idx_334_);
v___x_341_ = lean_uint8_dec_eq(v_got_340_, v___x_339_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v_a_332_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_354_; 
lean_inc(v_idx_334_);
lean_inc_ref(v_array_333_);
v_isSharedCheck_354_ = !lean_is_exclusive(v_a_332_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_355_ = lean_ctor_get(v_a_332_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_a_332_, 0);
lean_dec(v_unused_356_);
v___x_345_ = v_a_332_;
v_isShared_346_ = v_isSharedCheck_354_;
goto v_resetjp_344_;
}
else
{
lean_dec(v_a_332_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_354_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_idx_334_, v___x_347_);
lean_dec(v_idx_334_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_348_);
v___x_350_ = v___x_345_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_array_333_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_353_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_pos_364_; lean_object* v_pos_368_; lean_object* v_maxSpaceSequence_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_snd_375_; lean_object* v_snd_376_; uint8_t v___x_377_; 
v_maxSpaceSequence_371_ = lean_ctor_get(v_limits_361_, 8);
v___x_372_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_372_, v_maxSpaceSequence_371_, v___x_373_, v_a_362_);
v_snd_375_ = lean_ctor_get(v___x_374_, 1);
lean_inc(v_snd_375_);
lean_dec_ref(v___x_374_);
v_snd_376_ = lean_ctor_get(v_snd_375_, 1);
v___x_377_ = lean_unbox(v_snd_376_);
if (v___x_377_ == 0)
{
lean_object* v_fst_378_; lean_object* v_array_379_; lean_object* v_idx_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_fst_378_ = lean_ctor_get(v_snd_375_, 0);
lean_inc(v_fst_378_);
lean_dec(v_snd_375_);
v_array_379_ = lean_ctor_get(v_fst_378_, 0);
v_idx_380_ = lean_ctor_get(v_fst_378_, 1);
v___x_381_ = lean_byte_array_size(v_array_379_);
v___x_382_ = lean_nat_dec_lt(v_idx_380_, v___x_381_);
if (v___x_382_ == 0)
{
v_pos_364_ = v_fst_378_;
goto v___jp_363_;
}
else
{
uint8_t v___x_383_; uint32_t v___x_384_; uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_383_ = lean_byte_array_fget(v_array_379_, v_idx_380_);
v___x_384_ = lean_uint8_to_uint32(v___x_383_);
v___x_385_ = 32;
v___x_386_ = lean_uint32_dec_eq(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 9;
v___x_388_ = lean_uint32_dec_eq(v___x_384_, v___x_387_);
if (v___x_388_ == 0)
{
v_pos_364_ = v_fst_378_;
goto v___jp_363_;
}
else
{
v_pos_368_ = v_fst_378_;
goto v___jp_367_;
}
}
else
{
v_pos_368_ = v_fst_378_;
goto v___jp_367_;
}
}
}
else
{
lean_object* v_fst_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_397_; 
v_fst_389_ = lean_ctor_get(v_snd_375_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v_snd_375_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_snd_375_, 1);
lean_dec(v_unused_398_);
v___x_391_ = v_snd_375_;
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_fst_389_);
lean_dec(v_snd_375_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_box(0);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 1);
lean_ctor_set(v___x_391_, 1, v___x_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_fst_389_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
v___jp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_pos_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
return v___x_366_;
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v_pos_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_399_, v_a_400_);
lean_dec_ref(v_limits_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_403_){
_start:
{
lean_object* v_array_404_; lean_object* v_idx_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_array_404_ = lean_ctor_get(v_a_403_, 0);
v_idx_405_ = lean_ctor_get(v_a_403_, 1);
v___x_406_ = lean_byte_array_size(v_array_404_);
v___x_407_ = lean_nat_dec_lt(v_idx_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v_a_403_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
return v___x_409_;
}
else
{
lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_465_; 
lean_inc(v_idx_405_);
lean_inc_ref(v_array_404_);
v_isSharedCheck_465_ = !lean_is_exclusive(v_a_403_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_466_ = lean_ctor_get(v_a_403_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_a_403_, 0);
lean_dec(v_unused_467_);
v___x_411_ = v_a_403_;
v_isShared_412_ = v_isSharedCheck_465_;
goto v_resetjp_410_;
}
else
{
lean_dec(v_a_403_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_465_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
uint8_t v_c_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_it_x27_417_; 
v_c_413_ = lean_byte_array_fget(v_array_404_, v_idx_405_);
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_add(v_idx_405_, v___x_414_);
lean_dec(v_idx_405_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_415_);
v_it_x27_417_ = v___x_411_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_array_404_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_415_);
v_it_x27_417_ = v_reuseFailAlloc_464_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
uint8_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = 48;
v___x_461_ = lean_uint8_dec_le(v___x_460_, v_c_413_);
if (v___x_461_ == 0)
{
goto v___jp_455_;
}
else
{
uint8_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = 57;
v___x_463_ = lean_uint8_dec_le(v_c_413_, v___x_462_);
if (v___x_463_ == 0)
{
goto v___jp_455_;
}
else
{
goto v___jp_435_;
}
}
v___jp_418_:
{
uint8_t v___x_419_; uint8_t v___x_420_; uint8_t v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_419_ = 97;
v___x_420_ = lean_uint8_sub(v_c_413_, v___x_419_);
v___x_421_ = 10;
v___x_422_ = lean_uint8_add(v___x_420_, v___x_421_);
v___x_423_ = lean_box(v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_it_x27_417_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
return v___x_424_;
}
v___jp_425_:
{
uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_426_ = 65;
v___x_427_ = lean_uint8_dec_le(v___x_426_, v_c_413_);
if (v___x_427_ == 0)
{
goto v___jp_418_;
}
else
{
uint8_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = 70;
v___x_429_ = lean_uint8_dec_le(v_c_413_, v___x_428_);
if (v___x_429_ == 0)
{
goto v___jp_418_;
}
else
{
uint8_t v___x_430_; uint8_t v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_430_ = lean_uint8_sub(v_c_413_, v___x_426_);
v___x_431_ = 10;
v___x_432_ = lean_uint8_add(v___x_430_, v___x_431_);
v___x_433_ = lean_box(v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v_it_x27_417_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
return v___x_434_;
}
}
}
v___jp_435_:
{
uint8_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = 48;
v___x_437_ = lean_uint8_dec_le(v___x_436_, v_c_413_);
if (v___x_437_ == 0)
{
goto v___jp_425_;
}
else
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 57;
v___x_439_ = lean_uint8_dec_le(v_c_413_, v___x_438_);
if (v___x_439_ == 0)
{
goto v___jp_425_;
}
else
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_uint8_sub(v_c_413_, v___x_436_);
v___x_441_ = lean_box(v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_it_x27_417_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
}
}
v___jp_443_:
{
lean_object* v___x_444_; uint32_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_444_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0));
v___x_445_ = lean_uint8_to_uint32(v_c_413_);
v___x_446_ = l_Char_quote(v___x_445_);
v___x_447_ = lean_string_append(v___x_444_, v___x_446_);
lean_dec_ref(v___x_446_);
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v_it_x27_417_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
return v___x_449_;
}
v___jp_450_:
{
uint8_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 65;
v___x_452_ = lean_uint8_dec_le(v___x_451_, v_c_413_);
if (v___x_452_ == 0)
{
goto v___jp_443_;
}
else
{
uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 70;
v___x_454_ = lean_uint8_dec_le(v_c_413_, v___x_453_);
if (v___x_454_ == 0)
{
goto v___jp_443_;
}
else
{
goto v___jp_435_;
}
}
}
v___jp_455_:
{
uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = 97;
v___x_457_ = lean_uint8_dec_le(v___x_456_, v_c_413_);
if (v___x_457_ == 0)
{
goto v___jp_450_;
}
else
{
uint8_t v___x_458_; uint8_t v___x_459_; 
v___x_458_ = 102;
v___x_459_ = lean_uint8_dec_le(v_c_413_, v___x_458_);
if (v___x_459_ == 0)
{
goto v___jp_450_;
}
else
{
goto v___jp_435_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object* v_acc_474_, lean_object* v_count_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_477_; 
lean_inc_ref(v_a_476_);
v___x_477_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_pos_478_; lean_object* v_res_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_496_; 
lean_dec_ref(v_a_476_);
v_pos_478_ = lean_ctor_get(v___x_477_, 0);
v_res_479_ = lean_ctor_get(v___x_477_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_496_ == 0)
{
v___x_481_ = v___x_477_;
v_isShared_482_ = v_isSharedCheck_496_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_res_479_);
lean_inc(v_pos_478_);
lean_dec(v___x_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_496_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_483_ = lean_unsigned_to_nat(16u);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_count_475_, v___x_484_);
lean_dec(v_count_475_);
v___x_486_ = lean_nat_dec_lt(v___x_483_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_del_object(v___x_481_);
v___x_487_ = lean_nat_mul(v_acc_474_, v___x_483_);
lean_dec(v_acc_474_);
v___x_488_ = lean_unbox(v_res_479_);
lean_dec(v_res_479_);
v___x_489_ = lean_uint8_to_nat(v___x_488_);
v___x_490_ = lean_nat_add(v___x_487_, v___x_489_);
lean_dec(v___x_487_);
v_acc_474_ = v___x_490_;
v_count_475_ = v___x_485_;
v_a_476_ = v_pos_478_;
goto _start;
}
else
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v___x_485_);
lean_dec(v_res_479_);
lean_dec(v_acc_474_);
v___x_492_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 1);
lean_ctor_set(v___x_481_, 1, v___x_492_);
v___x_494_ = v___x_481_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_pos_478_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_err_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_522_; 
v_err_497_ = lean_ctor_get(v___x_477_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v___x_477_, 0);
lean_dec(v_unused_523_);
v___x_499_ = v___x_477_;
v_isShared_500_ = v_isSharedCheck_522_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_err_497_);
lean_dec(v___x_477_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_522_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_array_501_; lean_object* v_idx_502_; uint8_t v___x_503_; 
v_array_501_ = lean_ctor_get(v_a_476_, 0);
v_idx_502_ = lean_ctor_get(v_a_476_, 1);
v___x_503_ = lean_nat_dec_eq(v_idx_502_, v_idx_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v_count_475_);
lean_dec(v_acc_474_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_a_476_);
v___x_505_ = v___x_499_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_476_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_err_497_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v___x_507_; uint8_t v___x_508_; 
lean_dec(v_err_497_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_nat_dec_eq(v_count_475_, v___x_507_);
lean_dec(v_count_475_);
if (v___x_508_ == 0)
{
lean_object* v___x_510_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 0);
lean_ctor_set(v___x_499_, 1, v_acc_474_);
lean_ctor_set(v___x_499_, 0, v_a_476_);
v___x_510_ = v___x_499_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_476_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_acc_474_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v___x_512_; uint8_t v___x_513_; 
lean_dec(v_acc_474_);
v___x_512_ = lean_byte_array_size(v_array_501_);
v___x_513_ = lean_nat_dec_lt(v_idx_502_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_box(0);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___x_514_);
lean_ctor_set(v___x_499_, 0, v_a_476_);
v___x_516_ = v___x_499_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_476_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___x_518_);
lean_ctor_set(v___x_499_, 0, v_a_476_);
v___x_520_ = v___x_499_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_476_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_525_, v___x_525_, v_a_524_);
return v___x_526_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_529_ = lean_string_to_utf8(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_538_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_537_, v_a_536_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_pos_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_600_; 
v_pos_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_538_, 1);
lean_dec(v_unused_601_);
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_600_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_pos_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_600_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_array_548_; lean_object* v_idx_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_array_548_ = lean_ctor_get(v_pos_539_, 0);
v_idx_549_ = lean_ctor_get(v_pos_539_, 1);
v___x_550_ = lean_byte_array_size(v_array_548_);
v___x_551_ = lean_nat_dec_lt(v_idx_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_del_object(v___x_541_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v_pos_539_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
return v___x_553_;
}
else
{
uint8_t v_c_554_; uint8_t v___x_555_; uint8_t v___x_556_; 
v_c_554_ = lean_byte_array_fget(v_array_548_, v_idx_549_);
v___x_555_ = 48;
v___x_556_ = lean_uint8_dec_le(v___x_555_, v_c_554_);
if (v___x_556_ == 0)
{
goto v___jp_543_;
}
else
{
uint8_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = 57;
v___x_558_ = lean_uint8_dec_le(v_c_554_, v___x_557_);
if (v___x_558_ == 0)
{
goto v___jp_543_;
}
else
{
lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_597_; 
lean_inc(v_idx_549_);
lean_inc_ref(v_array_548_);
lean_del_object(v___x_541_);
v_isSharedCheck_597_ = !lean_is_exclusive(v_pos_539_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; lean_object* v_unused_599_; 
v_unused_598_ = lean_ctor_get(v_pos_539_, 1);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_pos_539_, 0);
lean_dec(v_unused_599_);
v___x_560_ = v_pos_539_;
v_isShared_561_ = v_isSharedCheck_597_;
goto v_resetjp_559_;
}
else
{
lean_dec(v_pos_539_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_597_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v_it_x27_565_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_idx_549_, v___x_562_);
lean_dec(v_idx_549_);
lean_inc(v___x_563_);
lean_inc_ref(v_array_548_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_563_);
v_it_x27_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_array_548_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_563_);
v_it_x27_565_ = v_reuseFailAlloc_596_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
uint8_t v___x_566_; 
v___x_566_ = lean_nat_dec_lt(v___x_563_, v___x_550_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_563_);
lean_dec_ref(v_array_548_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_568_, 0, v_it_x27_565_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
return v___x_568_;
}
else
{
uint8_t v___x_569_; uint8_t v_got_570_; uint8_t v___x_571_; 
v___x_569_ = 46;
v_got_570_ = lean_byte_array_fget(v_array_548_, v___x_563_);
v___x_571_ = lean_uint8_dec_eq(v_got_570_, v___x_569_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v___x_563_);
lean_dec_ref(v_array_548_);
v___x_572_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5));
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v_it_x27_565_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_579_; 
lean_dec_ref(v_it_x27_565_);
v___x_574_ = lean_nat_add(v___x_563_, v___x_562_);
lean_dec(v___x_563_);
lean_inc(v___x_574_);
lean_inc_ref(v_array_548_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_array_548_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_579_ = lean_nat_dec_lt(v___x_574_, v___x_550_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v___x_574_);
lean_dec_ref(v_array_548_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_575_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
return v___x_581_;
}
else
{
uint8_t v_c_582_; uint8_t v___x_583_; 
v_c_582_ = lean_byte_array_fget(v_array_548_, v___x_574_);
v___x_583_ = lean_uint8_dec_le(v___x_555_, v_c_582_);
if (v___x_583_ == 0)
{
lean_dec(v___x_574_);
lean_dec_ref(v_array_548_);
goto v___jp_576_;
}
else
{
uint8_t v___x_584_; 
v___x_584_ = lean_uint8_dec_le(v_c_582_, v___x_557_);
if (v___x_584_ == 0)
{
lean_dec(v___x_574_);
lean_dec_ref(v_array_548_);
goto v___jp_576_;
}
else
{
lean_object* v___x_585_; uint32_t v___x_586_; lean_object* v___x_587_; lean_object* v_it_x27_588_; uint32_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec_ref_known(v___x_575_, 2);
v___x_585_ = lean_unsigned_to_nat(48u);
v___x_586_ = lean_uint8_to_uint32(v_c_554_);
v___x_587_ = lean_nat_add(v___x_574_, v___x_562_);
lean_dec(v___x_574_);
v_it_x27_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_588_, 0, v_array_548_);
lean_ctor_set(v_it_x27_588_, 1, v___x_587_);
v___x_589_ = lean_uint8_to_uint32(v_c_582_);
v___x_590_ = lean_uint32_to_nat(v___x_586_);
v___x_591_ = lean_nat_sub(v___x_590_, v___x_585_);
lean_dec(v___x_590_);
v___x_592_ = lean_uint32_to_nat(v___x_589_);
v___x_593_ = lean_nat_sub(v___x_592_, v___x_585_);
lean_dec(v___x_592_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_591_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_it_x27_588_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
}
}
v___jp_576_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_575_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
}
}
}
}
}
}
}
v___jp_543_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
lean_ctor_set(v___x_541_, 1, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_pos_539_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_pos_602_; lean_object* v_err_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_pos_602_ = lean_ctor_get(v___x_538_, 0);
v_err_603_ = lean_ctor_get(v___x_538_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_538_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_err_603_);
lean_inc(v_pos_602_);
lean_dec(v___x_538_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_pos_602_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_err_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_res_613_; lean_object* v_pos_614_; lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_res_613_ = lean_ctor_get(v___x_612_, 1);
lean_inc(v_res_613_);
v_pos_614_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_pos_614_);
lean_dec_ref_known(v___x_612_, 2);
v_fst_615_ = lean_ctor_get(v_res_613_, 0);
lean_inc(v_fst_615_);
v_snd_616_ = lean_ctor_get(v_res_613_, 1);
lean_inc(v_snd_616_);
lean_dec(v_res_613_);
v___x_617_ = l_Std_Http_Version_ofNumber_x3f(v_fst_615_, v_snd_616_);
lean_dec(v_snd_616_);
lean_dec(v_fst_615_);
v___x_618_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_617_, v_pos_614_);
lean_dec(v___x_617_);
return v___x_618_;
}
else
{
lean_object* v_pos_619_; lean_object* v_err_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_pos_619_ = lean_ctor_get(v___x_612_, 0);
v_err_620_ = lean_ctor_get(v___x_612_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_612_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_err_620_);
lean_inc(v_pos_619_);
lean_dec(v___x_612_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_pos_619_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_err_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object* v_a_628_, lean_object* v_f_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_apply_1(v_a_628_, v___y_630_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_pos_632_; lean_object* v_res_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
v_pos_632_ = lean_ctor_get(v___x_631_, 0);
v_res_633_ = lean_ctor_get(v___x_631_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_641_ == 0)
{
v___x_635_ = v___x_631_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_res_633_);
lean_inc(v_pos_632_);
lean_dec(v___x_631_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_apply_1(v_f_629_, v_res_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_pos_632_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_pos_642_; lean_object* v_err_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_f_629_);
v_pos_642_ = lean_ctor_get(v___x_631_, 0);
v_err_643_ = lean_ctor_get(v___x_631_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_631_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_err_643_);
lean_inc(v_pos_642_);
lean_dec(v___x_631_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_pos_642_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_err_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_a_653_, lean_object* v_f_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v_a_653_, v_f_654_, v___y_655_);
return v___x_656_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object* v_x_657_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = 8;
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object* v_x_659_){
_start:
{
uint8_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_659_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object* v_x_662_){
_start:
{
uint8_t v___x_663_; 
v___x_663_ = 9;
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object* v_x_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = 7;
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object* v_x_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = 32;
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object* v_x_674_){
_start:
{
uint8_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_674_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object* v_x_677_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = 0;
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object* v_x_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_679_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object* v_x_682_){
_start:
{
uint8_t v___x_683_; 
v___x_683_ = 28;
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object* v_x_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_684_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object* v_x_687_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = 31;
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object* v_x_689_){
_start:
{
uint8_t v_res_690_; lean_object* v_r_691_; 
v_res_690_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_689_);
v_r_691_ = lean_box(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object* v_x_692_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = 1;
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object* v_x_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_694_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object* v_x_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = 2;
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object* v_x_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(v_x_699_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object* v_x_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = 5;
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object* v_x_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_704_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object* v_x_707_){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = 3;
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object* v_x_709_){
_start:
{
uint8_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_709_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object* v_x_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = 4;
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object* v_x_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_714_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object* v_x_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = 6;
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object* v_x_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_719_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object* v_x_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = 10;
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object* v_x_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_724_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object* v_x_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = 11;
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object* v_x_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object* v_x_732_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = 12;
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object* v_x_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_734_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object* v_x_737_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = 13;
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object* v_x_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_739_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object* v_x_742_){
_start:
{
uint8_t v___x_743_; 
v___x_743_ = 14;
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object* v_x_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = 15;
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_749_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object* v_x_752_){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = 16;
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object* v_x_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_754_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object* v_x_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = 17;
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_759_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object* v_x_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = 18;
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object* v_x_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object* v_x_767_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = 19;
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object* v_x_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_769_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object* v_x_772_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = 20;
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object* v_x_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_774_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object* v_x_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = 21;
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object* v_x_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_779_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object* v_x_782_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = 23;
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object* v_x_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object* v_x_787_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = 27;
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object* v_x_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object* v_x_792_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = 22;
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object* v_x_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object* v_x_797_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = 24;
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object* v_x_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_799_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object* v_x_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = 25;
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object* v_x_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_804_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object* v_x_807_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = 26;
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object* v_x_809_){
_start:
{
uint8_t v_res_810_; lean_object* v_r_811_; 
v_res_810_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_809_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object* v_x_812_){
_start:
{
uint8_t v___x_813_; 
v___x_813_ = 29;
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object* v_x_814_){
_start:
{
uint8_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_814_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = 30;
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object* v_x_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_819_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object* v_x_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = 33;
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object* v_x_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_824_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object* v_x_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = 34;
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object* v_x_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object* v_x_832_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = 35;
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object* v_x_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object* v_x_837_){
_start:
{
uint8_t v___x_838_; 
v___x_838_ = 36;
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object* v_x_839_){
_start:
{
uint8_t v_res_840_; lean_object* v_r_841_; 
v_res_840_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_839_);
v_r_841_ = lean_box(v_res_840_);
return v_r_841_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object* v_x_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = 38;
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object* v_x_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_844_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object* v_x_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = 37;
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object* v_x_849_){
_start:
{
uint8_t v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_849_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object* v_x_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = 39;
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object* v_x_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_854_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___x_860_ = lean_string_to_utf8(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2);
v___x_862_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5));
v___x_866_ = lean_string_to_utf8(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6);
v___x_868_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9));
v___x_872_ = lean_string_to_utf8(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10);
v___x_874_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13));
v___x_878_ = lean_string_to_utf8(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14);
v___x_880_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17));
v___x_884_ = lean_string_to_utf8(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18);
v___x_886_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21));
v___x_890_ = lean_string_to_utf8(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22);
v___x_892_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25));
v___x_896_ = lean_string_to_utf8(v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26);
v___x_898_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29));
v___x_902_ = lean_string_to_utf8(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30);
v___x_904_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33));
v___x_908_ = lean_string_to_utf8(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34);
v___x_910_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37));
v___x_914_ = lean_string_to_utf8(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38);
v___x_916_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41));
v___x_920_ = lean_string_to_utf8(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42);
v___x_922_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45));
v___x_926_ = lean_string_to_utf8(v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46);
v___x_928_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49));
v___x_932_ = lean_string_to_utf8(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50);
v___x_934_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53));
v___x_938_ = lean_string_to_utf8(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54);
v___x_940_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57));
v___x_944_ = lean_string_to_utf8(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58);
v___x_946_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61));
v___x_950_ = lean_string_to_utf8(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62);
v___x_952_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65));
v___x_956_ = lean_string_to_utf8(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66);
v___x_958_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69));
v___x_962_ = lean_string_to_utf8(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70);
v___x_964_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73));
v___x_968_ = lean_string_to_utf8(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74);
v___x_970_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77));
v___x_974_ = lean_string_to_utf8(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78);
v___x_976_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81));
v___x_980_ = lean_string_to_utf8(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82);
v___x_982_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85));
v___x_986_ = lean_string_to_utf8(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86);
v___x_988_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89));
v___x_992_ = lean_string_to_utf8(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90);
v___x_994_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93));
v___x_998_ = lean_string_to_utf8(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94);
v___x_1000_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97));
v___x_1004_ = lean_string_to_utf8(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98);
v___x_1006_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101));
v___x_1010_ = lean_string_to_utf8(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102);
v___x_1012_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105));
v___x_1016_ = lean_string_to_utf8(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106);
v___x_1018_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109));
v___x_1022_ = lean_string_to_utf8(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110);
v___x_1024_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113));
v___x_1028_ = lean_string_to_utf8(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114);
v___x_1030_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117));
v___x_1034_ = lean_string_to_utf8(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118);
v___x_1036_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121));
v___x_1040_ = lean_string_to_utf8(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122);
v___x_1042_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125));
v___x_1046_ = lean_string_to_utf8(v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126);
v___x_1048_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129));
v___x_1052_ = lean_string_to_utf8(v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130);
v___x_1054_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133));
v___x_1058_ = lean_string_to_utf8(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134);
v___x_1060_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137));
v___x_1064_ = lean_string_to_utf8(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138);
v___x_1066_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141));
v___x_1070_ = lean_string_to_utf8(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142);
v___x_1072_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145));
v___x_1076_ = lean_string_to_utf8(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146);
v___x_1078_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149));
v___x_1082_ = lean_string_to_utf8(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150);
v___x_1084_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153));
v___x_1088_ = lean_string_to_utf8(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154);
v___x_1090_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157));
v___x_1094_ = lean_string_to_utf8(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158);
v___x_1096_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___f_1101_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0));
v___x_1102_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3);
lean_inc_ref(v_a_1100_);
v___x_1103_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1102_, v___f_1101_, v_a_1100_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1103_;
}
else
{
lean_object* v_err_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1259_; 
v_err_1104_ = lean_ctor_get(v___x_1103_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1103_, 0);
lean_dec(v_unused_1260_);
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1259_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_err_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1259_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_idx_1108_; uint8_t v___x_1109_; 
v_idx_1108_ = lean_ctor_get(v_a_1100_, 1);
v___x_1109_ = lean_nat_dec_eq(v_idx_1108_, v_idx_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1111_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v_a_1100_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1100_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_err_1104_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
else
{
lean_object* v___f_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_del_object(v___x_1106_);
lean_dec(v_err_1104_);
v___f_1113_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4));
v___x_1114_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7);
lean_inc_ref(v_a_1100_);
v___x_1115_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1114_, v___f_1113_, v_a_1100_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1115_;
}
else
{
lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec_ref_known(v___x_1115_, 2);
v___f_1116_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8));
v___x_1117_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11);
lean_inc_ref(v_a_1100_);
v___x_1118_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1117_, v___f_1116_, v_a_1100_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1118_;
}
else
{
lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref_known(v___x_1118_, 2);
v___f_1119_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12));
v___x_1120_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15);
lean_inc_ref(v_a_1100_);
v___x_1121_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1120_, v___f_1119_, v_a_1100_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1121_;
}
else
{
lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec_ref_known(v___x_1121_, 2);
v___f_1122_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16));
v___x_1123_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19);
lean_inc_ref(v_a_1100_);
v___x_1124_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1123_, v___f_1122_, v_a_1100_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1124_;
}
else
{
lean_object* v___f_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref_known(v___x_1124_, 2);
v___f_1125_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20));
v___x_1126_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23);
lean_inc_ref(v_a_1100_);
v___x_1127_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1126_, v___f_1125_, v_a_1100_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1127_;
}
else
{
lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec_ref_known(v___x_1127_, 2);
v___f_1128_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24));
v___x_1129_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27);
lean_inc_ref(v_a_1100_);
v___x_1130_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1129_, v___f_1128_, v_a_1100_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1130_;
}
else
{
lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec_ref_known(v___x_1130_, 2);
v___f_1131_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28));
v___x_1132_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31);
lean_inc_ref(v_a_1100_);
v___x_1133_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1132_, v___f_1131_, v_a_1100_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1133_;
}
else
{
lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref_known(v___x_1133_, 2);
v___f_1134_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32));
v___x_1135_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35);
lean_inc_ref(v_a_1100_);
v___x_1136_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1135_, v___f_1134_, v_a_1100_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1136_;
}
else
{
lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec_ref_known(v___x_1136_, 2);
v___f_1137_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36));
v___x_1138_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39);
lean_inc_ref(v_a_1100_);
v___x_1139_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1138_, v___f_1137_, v_a_1100_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1139_;
}
else
{
lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref_known(v___x_1139_, 2);
v___f_1140_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40));
v___x_1141_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43);
lean_inc_ref(v_a_1100_);
v___x_1142_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1141_, v___f_1140_, v_a_1100_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1142_;
}
else
{
lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref_known(v___x_1142_, 2);
v___f_1143_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44));
v___x_1144_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47);
lean_inc_ref(v_a_1100_);
v___x_1145_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1144_, v___f_1143_, v_a_1100_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1145_;
}
else
{
lean_object* v___f_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref_known(v___x_1145_, 2);
v___f_1146_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48));
v___x_1147_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51);
lean_inc_ref(v_a_1100_);
v___x_1148_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1147_, v___f_1146_, v_a_1100_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1148_;
}
else
{
lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref_known(v___x_1148_, 2);
v___f_1149_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52));
v___x_1150_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55);
lean_inc_ref(v_a_1100_);
v___x_1151_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1150_, v___f_1149_, v_a_1100_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1151_;
}
else
{
lean_object* v___f_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref_known(v___x_1151_, 2);
v___f_1152_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56));
v___x_1153_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59);
lean_inc_ref(v_a_1100_);
v___x_1154_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1153_, v___f_1152_, v_a_1100_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1154_;
}
else
{
lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref_known(v___x_1154_, 2);
v___f_1155_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60));
v___x_1156_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63);
lean_inc_ref(v_a_1100_);
v___x_1157_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1156_, v___f_1155_, v_a_1100_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1157_;
}
else
{
lean_object* v___f_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref_known(v___x_1157_, 2);
v___f_1158_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64));
v___x_1159_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67);
lean_inc_ref(v_a_1100_);
v___x_1160_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1159_, v___f_1158_, v_a_1100_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1160_;
}
else
{
lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec_ref_known(v___x_1160_, 2);
v___f_1161_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68));
v___x_1162_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71);
lean_inc_ref(v_a_1100_);
v___x_1163_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1162_, v___f_1161_, v_a_1100_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1163_;
}
else
{
lean_object* v___f_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref_known(v___x_1163_, 2);
v___f_1164_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72));
v___x_1165_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75);
lean_inc_ref(v_a_1100_);
v___x_1166_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1165_, v___f_1164_, v_a_1100_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1166_;
}
else
{
lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec_ref_known(v___x_1166_, 2);
v___f_1167_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76));
v___x_1168_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79);
lean_inc_ref(v_a_1100_);
v___x_1169_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1168_, v___f_1167_, v_a_1100_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1169_;
}
else
{
lean_object* v___f_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec_ref_known(v___x_1169_, 2);
v___f_1170_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80));
v___x_1171_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83);
lean_inc_ref(v_a_1100_);
v___x_1172_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1171_, v___f_1170_, v_a_1100_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1172_;
}
else
{
lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref_known(v___x_1172_, 2);
v___f_1173_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84));
v___x_1174_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87);
lean_inc_ref(v_a_1100_);
v___x_1175_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1174_, v___f_1173_, v_a_1100_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1175_;
}
else
{
lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref_known(v___x_1175_, 2);
v___f_1176_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88));
v___x_1177_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91);
lean_inc_ref(v_a_1100_);
v___x_1178_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1177_, v___f_1176_, v_a_1100_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1178_;
}
else
{
lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec_ref_known(v___x_1178_, 2);
v___f_1179_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92));
v___x_1180_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95);
lean_inc_ref(v_a_1100_);
v___x_1181_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1180_, v___f_1179_, v_a_1100_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1181_;
}
else
{
lean_object* v___f_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec_ref_known(v___x_1181_, 2);
v___f_1182_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96));
v___x_1183_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99);
lean_inc_ref(v_a_1100_);
v___x_1184_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1183_, v___f_1182_, v_a_1100_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1184_;
}
else
{
lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref_known(v___x_1184_, 2);
v___f_1185_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100));
v___x_1186_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103);
lean_inc_ref(v_a_1100_);
v___x_1187_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1186_, v___f_1185_, v_a_1100_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1187_;
}
else
{
lean_object* v___f_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec_ref_known(v___x_1187_, 2);
v___f_1188_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104));
v___x_1189_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107);
lean_inc_ref(v_a_1100_);
v___x_1190_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1189_, v___f_1188_, v_a_1100_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1190_;
}
else
{
lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref_known(v___x_1190_, 2);
v___f_1191_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108));
v___x_1192_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111);
lean_inc_ref(v_a_1100_);
v___x_1193_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1192_, v___f_1191_, v_a_1100_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1193_;
}
else
{
lean_object* v___f_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref_known(v___x_1193_, 2);
v___f_1194_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112));
v___x_1195_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115);
lean_inc_ref(v_a_1100_);
v___x_1196_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1195_, v___f_1194_, v_a_1100_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1196_;
}
else
{
lean_object* v___f_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec_ref_known(v___x_1196_, 2);
v___f_1197_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116));
v___x_1198_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119);
lean_inc_ref(v_a_1100_);
v___x_1199_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1198_, v___f_1197_, v_a_1100_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1199_;
}
else
{
lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec_ref_known(v___x_1199_, 2);
v___f_1200_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120));
v___x_1201_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123);
lean_inc_ref(v_a_1100_);
v___x_1202_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1201_, v___f_1200_, v_a_1100_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1202_;
}
else
{
lean_object* v___f_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref_known(v___x_1202_, 2);
v___f_1203_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124));
v___x_1204_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127);
lean_inc_ref(v_a_1100_);
v___x_1205_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1204_, v___f_1203_, v_a_1100_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1205_;
}
else
{
lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_dec_ref_known(v___x_1205_, 2);
v___f_1206_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128));
v___x_1207_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131);
lean_inc_ref(v_a_1100_);
v___x_1208_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1207_, v___f_1206_, v_a_1100_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1208_;
}
else
{
lean_object* v___f_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref_known(v___x_1208_, 2);
v___f_1209_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132));
v___x_1210_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135);
lean_inc_ref(v_a_1100_);
v___x_1211_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1210_, v___f_1209_, v_a_1100_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1211_;
}
else
{
lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec_ref_known(v___x_1211_, 2);
v___f_1212_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136));
v___x_1213_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139);
lean_inc_ref(v_a_1100_);
v___x_1214_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1213_, v___f_1212_, v_a_1100_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1214_;
}
else
{
lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref_known(v___x_1214_, 2);
v___f_1215_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140));
v___x_1216_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143);
lean_inc_ref(v_a_1100_);
v___x_1217_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1216_, v___f_1215_, v_a_1100_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1217_;
}
else
{
lean_object* v___f_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref_known(v___x_1217_, 2);
v___f_1218_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144));
v___x_1219_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147);
lean_inc_ref(v_a_1100_);
v___x_1220_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1219_, v___f_1218_, v_a_1100_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1220_;
}
else
{
lean_object* v___f_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec_ref_known(v___x_1220_, 2);
v___f_1221_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148));
v___x_1222_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151);
lean_inc_ref(v_a_1100_);
v___x_1223_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1222_, v___f_1221_, v_a_1100_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1223_;
}
else
{
lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref_known(v___x_1223_, 2);
v___f_1224_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152));
v___x_1225_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155);
lean_inc_ref(v_a_1100_);
v___x_1226_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1225_, v___f_1224_, v_a_1100_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1226_;
}
else
{
lean_object* v___f_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref_known(v___x_1226_, 2);
v___f_1227_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156));
v___x_1228_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159);
lean_inc_ref(v_a_1100_);
v___x_1229_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1228_, v___f_1227_, v_a_1100_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_dec_ref(v_a_1100_);
return v___x_1229_;
}
else
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1256_; 
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; lean_object* v_unused_1258_; 
v_unused_1257_ = lean_ctor_get(v___x_1229_, 1);
lean_dec(v_unused_1257_);
v_unused_1258_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1258_);
v___x_1231_ = v___x_1229_;
v_isShared_1232_ = v_isSharedCheck_1256_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1256_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_snd_1237_; lean_object* v_snd_1238_; uint8_t v___x_1239_; 
v___f_1233_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1234_ = lean_unsigned_to_nat(64u);
v___x_1235_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1100_);
v___x_1236_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1233_, v___x_1234_, v___x_1235_, v_a_1100_);
v_snd_1237_ = lean_ctor_get(v___x_1236_, 1);
lean_inc(v_snd_1237_);
v_snd_1238_ = lean_ctor_get(v_snd_1237_, 1);
v___x_1239_ = lean_unbox(v_snd_1238_);
if (v___x_1239_ == 0)
{
lean_object* v_fst_1240_; lean_object* v_fst_1241_; uint8_t v___x_1242_; 
v_fst_1240_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_fst_1240_);
lean_dec_ref(v___x_1236_);
v_fst_1241_ = lean_ctor_get(v_snd_1237_, 0);
lean_inc(v_fst_1241_);
lean_dec(v_snd_1237_);
v___x_1242_ = lean_nat_dec_eq(v_fst_1240_, v___x_1235_);
lean_dec(v_fst_1240_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_dec_ref(v_a_1100_);
v___x_1243_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161));
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1243_);
lean_ctor_set(v___x_1231_, 0, v_fst_1241_);
v___x_1245_ = v___x_1231_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_fst_1241_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec(v_fst_1241_);
v___x_1247_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1247_);
lean_ctor_set(v___x_1231_, 0, v_a_1100_);
v___x_1249_ = v___x_1231_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1100_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_object* v_fst_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec_ref(v___x_1236_);
lean_dec_ref(v_a_1100_);
v_fst_1251_ = lean_ctor_get(v_snd_1237_, 0);
lean_inc(v_fst_1251_);
lean_dec(v_snd_1237_);
v___x_1252_ = lean_box(0);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1252_);
lean_ctor_set(v___x_1231_, 0, v_fst_1251_);
v___x_1254_ = v___x_1231_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_fst_1251_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1261_){
_start:
{
uint8_t v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = 32;
v___x_1263_ = lean_uint8_dec_eq(v_b_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = 1;
return v___x_1264_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1266_){
_start:
{
uint8_t v_b_boxed_1267_; uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_b_boxed_1267_ = lean_unbox(v_b_1266_);
v_res_1268_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1267_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v_maxUriLength_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_snd_1285_; lean_object* v_snd_1286_; uint8_t v___x_1287_; 
v_maxUriLength_1281_ = lean_ctor_get(v_limits_1274_, 4);
v___f_1282_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_1283_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1275_);
v___x_1284_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1282_, v_maxUriLength_1281_, v___x_1283_, v_a_1275_);
v_snd_1285_ = lean_ctor_get(v___x_1284_, 1);
lean_inc(v_snd_1285_);
v_snd_1286_ = lean_ctor_get(v_snd_1285_, 1);
v___x_1287_ = lean_unbox(v_snd_1286_);
if (v___x_1287_ == 0)
{
lean_object* v_fst_1288_; lean_object* v_fst_1289_; lean_object* v_array_1290_; lean_object* v_idx_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1318_; 
v_fst_1288_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_fst_1288_);
lean_dec_ref(v___x_1284_);
v_fst_1289_ = lean_ctor_get(v_snd_1285_, 0);
lean_inc(v_fst_1289_);
lean_dec(v_snd_1285_);
v_array_1290_ = lean_ctor_get(v_a_1275_, 0);
v_idx_1291_ = lean_ctor_get(v_a_1275_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_a_1275_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1293_ = v_a_1275_;
v_isShared_1294_ = v_isSharedCheck_1318_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_idx_1291_);
lean_inc(v_array_1290_);
lean_dec(v_a_1275_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1318_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_lower_1296_; lean_object* v_upper_1297_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___y_1315_; uint8_t v___x_1317_; 
v___x_1312_ = lean_nat_add(v_idx_1291_, v_fst_1288_);
lean_dec(v_fst_1288_);
v___x_1313_ = lean_byte_array_size(v_array_1290_);
v___x_1317_ = lean_nat_dec_le(v_idx_1291_, v___x_1283_);
if (v___x_1317_ == 0)
{
v___y_1315_ = v_idx_1291_;
goto v___jp_1314_;
}
else
{
lean_dec(v_idx_1291_);
v___y_1315_ = v___x_1283_;
goto v___jp_1314_;
}
v___jp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1298_ = l_ByteArray_toByteSlice(v_array_1290_, v_lower_1296_, v_upper_1297_);
v___x_1299_ = l_ByteSlice_size(v___x_1298_);
v___x_1300_ = lean_nat_dec_eq(v___x_1299_, v_maxUriLength_1281_);
lean_dec(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_del_object(v___x_1293_);
v___y_1277_ = v___x_1298_;
v___y_1278_ = v_fst_1289_;
goto v___jp_1276_;
}
else
{
lean_object* v_array_1301_; lean_object* v_idx_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_array_1301_ = lean_ctor_get(v_fst_1289_, 0);
v_idx_1302_ = lean_ctor_get(v_fst_1289_, 1);
v___x_1303_ = lean_byte_array_size(v_array_1301_);
v___x_1304_ = lean_nat_dec_lt(v_idx_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_del_object(v___x_1293_);
v___y_1277_ = v___x_1298_;
v___y_1278_ = v_fst_1289_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1305_; uint8_t v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = lean_byte_array_fget(v_array_1301_, v_idx_1302_);
v___x_1306_ = 32;
v___x_1307_ = lean_uint8_dec_eq(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec_ref(v___x_1298_);
v___x_1308_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 1);
lean_ctor_set(v___x_1293_, 1, v___x_1308_);
lean_ctor_set(v___x_1293_, 0, v_fst_1289_);
v___x_1310_ = v___x_1293_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_fst_1289_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
else
{
lean_del_object(v___x_1293_);
v___y_1277_ = v___x_1298_;
v___y_1278_ = v_fst_1289_;
goto v___jp_1276_;
}
}
}
}
v___jp_1314_:
{
uint8_t v___x_1316_; 
v___x_1316_ = lean_nat_dec_le(v___x_1312_, v___x_1313_);
if (v___x_1316_ == 0)
{
lean_dec(v___x_1312_);
v_lower_1296_ = v___y_1315_;
v_upper_1297_ = v___x_1313_;
goto v___jp_1295_;
}
else
{
v_lower_1296_ = v___y_1315_;
v_upper_1297_ = v___x_1312_;
goto v___jp_1295_;
}
}
}
}
else
{
lean_object* v_fst_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v___x_1284_);
lean_dec_ref(v_a_1275_);
v_fst_1319_ = lean_ctor_get(v_snd_1285_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_snd_1285_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_snd_1285_, 1);
lean_dec(v_unused_1328_);
v___x_1321_ = v_snd_1285_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_fst_1319_);
lean_dec(v_snd_1285_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_box(0);
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 1);
lean_ctor_set(v___x_1321_, 1, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_fst_1319_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
v___jp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = l_ByteSlice_toByteArray(v___y_1277_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___y_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1329_, v_a_1330_);
lean_dec_ref(v_limits_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_pos_1338_; lean_object* v_array_1339_; lean_object* v_idx_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_pos_1338_ = lean_ctor_get(v___x_1337_, 0);
v_array_1339_ = lean_ctor_get(v_pos_1338_, 0);
v_idx_1340_ = lean_ctor_get(v_pos_1338_, 1);
v___x_1341_ = lean_byte_array_size(v_array_1339_);
v___x_1342_ = lean_nat_dec_lt(v_idx_1340_, v___x_1341_);
if (v___x_1342_ == 0)
{
return v___x_1337_;
}
else
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
lean_inc(v_pos_1338_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; 
v_unused_1351_ = lean_ctor_get(v___x_1337_, 1);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v___x_1337_, 0);
lean_dec(v_unused_1352_);
v___x_1344_ = v___x_1337_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v___x_1337_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 1);
lean_ctor_set(v___x_1344_, 1, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_pos_1338_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1363_, v_a_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_pos_1366_; lean_object* v_res_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1444_; 
v_pos_1366_ = lean_ctor_get(v___x_1365_, 0);
v_res_1367_ = lean_ctor_get(v___x_1365_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1369_ = v___x_1365_;
v_isShared_1370_ = v_isSharedCheck_1444_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_res_1367_);
lean_inc(v_pos_1366_);
lean_dec(v___x_1365_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1444_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_array_1371_; lean_object* v_idx_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_array_1371_ = lean_ctor_get(v_pos_1366_, 0);
v_idx_1372_ = lean_ctor_get(v_pos_1366_, 1);
v___x_1373_ = lean_byte_array_size(v_array_1371_);
v___x_1374_ = lean_nat_dec_lt(v_idx_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v_res_1367_);
v___x_1375_ = lean_box(0);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 1);
lean_ctor_set(v___x_1369_, 1, v___x_1375_);
v___x_1377_ = v___x_1369_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_pos_1366_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
uint8_t v___x_1379_; uint8_t v_got_1380_; uint8_t v___x_1381_; 
v___x_1379_ = 32;
v_got_1380_ = lean_byte_array_fget(v_array_1371_, v_idx_1372_);
v___x_1381_ = lean_uint8_dec_eq(v_got_1380_, v___x_1379_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_dec(v_res_1367_);
v___x_1382_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 1);
lean_ctor_set(v___x_1369_, 1, v___x_1382_);
v___x_1384_ = v___x_1369_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_pos_1366_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1441_; 
lean_inc(v_idx_1372_);
lean_inc_ref(v_array_1371_);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_pos_1366_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; lean_object* v_unused_1443_; 
v_unused_1442_ = lean_ctor_get(v_pos_1366_, 1);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_pos_1366_, 0);
lean_dec(v_unused_1443_);
v___x_1387_ = v_pos_1366_;
v_isShared_1388_ = v_isSharedCheck_1441_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v_pos_1366_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1441_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_add(v_idx_1372_, v___x_1389_);
lean_dec(v_idx_1372_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_array_1371_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___f_1393_; lean_object* v___x_1394_; 
v___f_1393_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_1394_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1393_, v_res_1367_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1405_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 1);
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 1);
lean_ctor_set(v___x_1369_, 1, v___x_1400_);
lean_ctor_set(v___x_1369_, 0, v___x_1392_);
v___x_1402_ = v___x_1369_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1407_; 
lean_del_object(v___x_1369_);
v_a_1406_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1407_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v___x_1392_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_pos_1408_; lean_object* v_res_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_pos_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_pos_1408_);
v_res_1409_ = lean_ctor_get(v___x_1407_, 1);
lean_inc(v_res_1409_);
lean_dec_ref_known(v___x_1407_, 2);
v___x_1410_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_1411_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1410_, v_pos_1408_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_pos_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1420_; 
v_pos_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v___x_1411_, 1);
lean_dec(v_unused_1421_);
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_pos_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_a_1406_);
lean_ctor_set(v___x_1416_, 1, v_res_1409_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_pos_1412_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_object* v_pos_1422_; lean_object* v_err_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_res_1409_);
lean_dec(v_a_1406_);
v_pos_1422_ = lean_ctor_get(v___x_1411_, 0);
v_err_1423_ = lean_ctor_get(v___x_1411_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1411_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_err_1423_);
lean_inc(v_pos_1422_);
lean_dec(v___x_1411_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_pos_1422_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_err_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v_pos_1431_; lean_object* v_err_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_a_1406_);
v_pos_1431_ = lean_ctor_get(v___x_1407_, 0);
v_err_1432_ = lean_ctor_get(v___x_1407_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1407_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_err_1432_);
lean_inc(v_pos_1431_);
lean_dec(v___x_1407_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_pos_1431_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_err_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
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
lean_object* v_pos_1445_; lean_object* v_err_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_pos_1445_ = lean_ctor_get(v___x_1365_, 0);
v_err_1446_ = lean_ctor_get(v___x_1365_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1365_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_err_1446_);
lean_inc(v_pos_1445_);
lean_dec(v___x_1365_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_pos_1445_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_err_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1454_, v_a_1455_);
lean_dec_ref(v_limits_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1460_, v_a_1461_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_pos_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1553_; 
v_pos_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v___x_1462_, 1);
lean_dec(v_unused_1554_);
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1553_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_pos_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1553_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1463_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_pos_1468_; lean_object* v_res_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1543_; 
v_pos_1468_ = lean_ctor_get(v___x_1467_, 0);
v_res_1469_ = lean_ctor_get(v___x_1467_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1471_ = v___x_1467_;
v_isShared_1472_ = v_isSharedCheck_1543_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_res_1469_);
lean_inc(v_pos_1468_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1543_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_array_1473_; lean_object* v_idx_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_array_1473_ = lean_ctor_get(v_pos_1468_, 0);
v_idx_1474_ = lean_ctor_get(v_pos_1468_, 1);
v___x_1475_ = lean_byte_array_size(v_array_1473_);
v___x_1476_ = lean_nat_dec_lt(v_idx_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec(v_res_1469_);
lean_del_object(v___x_1465_);
v___x_1477_ = lean_box(0);
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 1);
lean_ctor_set(v___x_1471_, 1, v___x_1477_);
v___x_1479_ = v___x_1471_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_pos_1468_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
else
{
uint8_t v___x_1481_; uint8_t v_got_1482_; uint8_t v___x_1483_; 
v___x_1481_ = 32;
v_got_1482_ = lean_byte_array_fget(v_array_1473_, v_idx_1474_);
v___x_1483_ = lean_uint8_dec_eq(v_got_1482_, v___x_1481_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
lean_dec(v_res_1469_);
lean_del_object(v___x_1465_);
v___x_1484_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 1);
lean_ctor_set(v___x_1471_, 1, v___x_1484_);
v___x_1486_ = v___x_1471_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_pos_1468_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
else
{
lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1540_; 
lean_inc(v_idx_1474_);
lean_inc_ref(v_array_1473_);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_pos_1468_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; lean_object* v_unused_1542_; 
v_unused_1541_ = lean_ctor_get(v_pos_1468_, 1);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_pos_1468_, 0);
lean_dec(v_unused_1542_);
v___x_1489_ = v_pos_1468_;
v_isShared_1490_ = v_isSharedCheck_1540_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v_pos_1468_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1540_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1491_ = lean_unsigned_to_nat(1u);
v___x_1492_ = lean_nat_add(v_idx_1474_, v___x_1491_);
lean_dec(v_idx_1474_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1492_);
v___x_1494_ = v___x_1489_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_array_1473_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; 
v___x_1495_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1460_, v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_pos_1496_; lean_object* v_res_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1529_; 
v_pos_1496_ = lean_ctor_get(v___x_1495_, 0);
v_res_1497_ = lean_ctor_get(v___x_1495_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1499_ = v___x_1495_;
v_isShared_1500_ = v_isSharedCheck_1529_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_res_1497_);
lean_inc(v_pos_1496_);
lean_dec(v___x_1495_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1529_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_snd_1506_; lean_object* v_fst_1507_; lean_object* v_fst_1508_; lean_object* v_snd_1509_; uint8_t v___x_1510_; 
v_snd_1506_ = lean_ctor_get(v_res_1497_, 1);
lean_inc(v_snd_1506_);
v_fst_1507_ = lean_ctor_get(v_res_1497_, 0);
lean_inc(v_fst_1507_);
lean_dec(v_res_1497_);
v_fst_1508_ = lean_ctor_get(v_snd_1506_, 0);
lean_inc(v_fst_1508_);
v_snd_1509_ = lean_ctor_get(v_snd_1506_, 1);
lean_inc(v_snd_1509_);
lean_dec(v_snd_1506_);
v___x_1510_ = lean_nat_dec_eq(v_fst_1508_, v___x_1491_);
lean_dec(v_fst_1508_);
if (v___x_1510_ == 0)
{
lean_del_object(v___x_1465_);
goto v___jp_1511_;
}
else
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_nat_dec_eq(v_snd_1509_, v___x_1491_);
if (v___x_1521_ == 0)
{
lean_del_object(v___x_1465_);
goto v___jp_1511_;
}
else
{
uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1527_; 
lean_dec(v_snd_1509_);
lean_del_object(v___x_1499_);
lean_del_object(v___x_1471_);
v___x_1522_ = 1;
v___x_1523_ = l_Std_Http_Headers_empty;
v___x_1524_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1524_, 0, v_fst_1507_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_unbox(v_res_1469_);
lean_dec(v_res_1469_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*2, v___x_1525_);
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*2 + 1, v___x_1522_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v___x_1524_);
lean_ctor_set(v___x_1465_, 0, v_pos_1496_);
v___x_1527_ = v___x_1465_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_pos_1496_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1524_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
v___jp_1501_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 1);
lean_ctor_set(v___x_1499_, 1, v___x_1502_);
v___x_1504_ = v___x_1499_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_pos_1496_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
v___jp_1511_:
{
if (v___x_1510_ == 0)
{
lean_dec(v_snd_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1471_);
lean_dec(v_res_1469_);
goto v___jp_1501_;
}
else
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_nat_dec_eq(v_snd_1509_, v___x_1512_);
lean_dec(v_snd_1509_);
if (v___x_1513_ == 0)
{
lean_dec(v_fst_1507_);
lean_del_object(v___x_1471_);
lean_dec(v_res_1469_);
goto v___jp_1501_;
}
else
{
uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1519_; 
lean_del_object(v___x_1499_);
v___x_1514_ = 0;
v___x_1515_ = l_Std_Http_Headers_empty;
v___x_1516_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1516_, 0, v_fst_1507_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = lean_unbox(v_res_1469_);
lean_dec(v_res_1469_);
lean_ctor_set_uint8(v___x_1516_, sizeof(void*)*2, v___x_1517_);
lean_ctor_set_uint8(v___x_1516_, sizeof(void*)*2 + 1, v___x_1514_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1516_);
lean_ctor_set(v___x_1471_, 0, v_pos_1496_);
v___x_1519_ = v___x_1471_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_pos_1496_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1516_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1530_; lean_object* v_err_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_del_object(v___x_1471_);
lean_dec(v_res_1469_);
lean_del_object(v___x_1465_);
v_pos_1530_ = lean_ctor_get(v___x_1495_, 0);
v_err_1531_ = lean_ctor_get(v___x_1495_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1495_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_err_1531_);
lean_inc(v_pos_1530_);
lean_dec(v___x_1495_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_pos_1530_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_err_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
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
lean_object* v_pos_1544_; lean_object* v_err_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_del_object(v___x_1465_);
v_pos_1544_ = lean_ctor_get(v___x_1467_, 0);
v_err_1545_ = lean_ctor_get(v___x_1467_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1467_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_err_1545_);
lean_inc(v_pos_1544_);
lean_dec(v___x_1467_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_pos_1544_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_err_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
else
{
lean_object* v_pos_1555_; lean_object* v_err_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_pos_1555_ = lean_ctor_get(v___x_1462_, 0);
v_err_1556_ = lean_ctor_get(v___x_1462_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1462_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_err_1556_);
lean_inc(v_pos_1555_);
lean_dec(v___x_1462_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_pos_1555_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_err_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_1564_, v_a_1565_);
lean_dec_ref(v_limits_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_pos_1570_; lean_object* v___x_1571_; 
v_pos_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_pos_1570_);
lean_dec_ref_known(v___x_1569_, 2);
v___x_1571_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_pos_1572_; lean_object* v_res_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1643_; 
v_pos_1572_ = lean_ctor_get(v___x_1571_, 0);
v_res_1573_ = lean_ctor_get(v___x_1571_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1575_ = v___x_1571_;
v_isShared_1576_ = v_isSharedCheck_1643_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_res_1573_);
lean_inc(v_pos_1572_);
lean_dec(v___x_1571_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1643_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_array_1577_; lean_object* v_idx_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v_array_1577_ = lean_ctor_get(v_pos_1572_, 0);
v_idx_1578_ = lean_ctor_get(v_pos_1572_, 1);
v___x_1579_ = lean_byte_array_size(v_array_1577_);
v___x_1580_ = lean_nat_dec_lt(v_idx_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_dec(v_res_1573_);
v___x_1581_ = lean_box(0);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 1);
lean_ctor_set(v___x_1575_, 1, v___x_1581_);
v___x_1583_ = v___x_1575_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_pos_1572_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
else
{
uint8_t v___x_1585_; uint8_t v_got_1586_; uint8_t v___x_1587_; 
v___x_1585_ = 32;
v_got_1586_ = lean_byte_array_fget(v_array_1577_, v_idx_1578_);
v___x_1587_ = lean_uint8_dec_eq(v_got_1586_, v___x_1585_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
lean_dec(v_res_1573_);
v___x_1588_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 1);
lean_ctor_set(v___x_1575_, 1, v___x_1588_);
v___x_1590_ = v___x_1575_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_pos_1572_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
else
{
lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1640_; 
lean_inc(v_idx_1578_);
lean_inc_ref(v_array_1577_);
lean_del_object(v___x_1575_);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_pos_1572_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; 
v_unused_1641_ = lean_ctor_get(v_pos_1572_, 1);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_pos_1572_, 0);
lean_dec(v_unused_1642_);
v___x_1593_ = v_pos_1572_;
v_isShared_1594_ = v_isSharedCheck_1640_;
goto v_resetjp_1592_;
}
else
{
lean_dec(v_pos_1572_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1640_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_unsigned_to_nat(1u);
v___x_1596_ = lean_nat_add(v_idx_1578_, v___x_1595_);
lean_dec(v_idx_1578_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_array_1577_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1567_, v___x_1598_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_res_1600_; lean_object* v_snd_1601_; lean_object* v_pos_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1628_; 
v_res_1600_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_res_1600_);
v_snd_1601_ = lean_ctor_get(v_res_1600_, 1);
lean_inc(v_snd_1601_);
v_pos_1602_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v___x_1599_, 1);
lean_dec(v_unused_1629_);
v___x_1604_ = v___x_1599_;
v_isShared_1605_ = v_isSharedCheck_1628_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_pos_1602_);
lean_dec(v___x_1599_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1628_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_fst_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1626_; 
v_fst_1606_ = lean_ctor_get(v_res_1600_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_res_1600_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v_res_1600_, 1);
lean_dec(v_unused_1627_);
v___x_1608_ = v_res_1600_;
v_isShared_1609_ = v_isSharedCheck_1626_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_fst_1606_);
lean_dec(v_res_1600_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1626_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v_fst_1610_; lean_object* v_snd_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1625_; 
v_fst_1610_ = lean_ctor_get(v_snd_1601_, 0);
v_snd_1611_ = lean_ctor_get(v_snd_1601_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_snd_1601_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1613_ = v_snd_1601_;
v_isShared_1614_ = v_isSharedCheck_1625_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_snd_1611_);
lean_inc(v_fst_1610_);
lean_dec(v_snd_1601_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1625_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = l_Std_Http_Version_ofNumber_x3f(v_fst_1610_, v_snd_1611_);
lean_dec(v_snd_1611_);
lean_dec(v_fst_1610_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 1, v___x_1615_);
lean_ctor_set(v___x_1613_, 0, v_fst_1606_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_fst_1606_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1619_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 1, v___x_1617_);
lean_ctor_set(v___x_1608_, 0, v_res_1573_);
v___x_1619_ = v___x_1608_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_res_1573_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 1, v___x_1619_);
v___x_1621_ = v___x_1604_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_pos_1602_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_1630_; lean_object* v_err_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_res_1573_);
v_pos_1630_ = lean_ctor_get(v___x_1599_, 0);
v_err_1631_ = lean_ctor_get(v___x_1599_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1599_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_err_1631_);
lean_inc(v_pos_1630_);
lean_dec(v___x_1599_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_pos_1630_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_err_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
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
lean_object* v_pos_1644_; lean_object* v_err_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_pos_1644_ = lean_ctor_get(v___x_1571_, 0);
v_err_1645_ = lean_ctor_get(v___x_1571_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1571_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_err_1645_);
lean_inc(v_pos_1644_);
lean_dec(v___x_1571_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_pos_1644_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_err_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_pos_1653_; lean_object* v_err_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_pos_1653_ = lean_ctor_get(v___x_1569_, 0);
v_err_1654_ = lean_ctor_get(v___x_1569_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1569_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_err_1654_);
lean_inc(v_pos_1653_);
lean_dec(v___x_1569_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_pos_1653_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_err_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_1662_, v_a_1663_);
lean_dec_ref(v_limits_1662_);
return v_res_1664_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_1665_){
_start:
{
uint32_t v___x_1666_; uint32_t v___x_1667_; uint8_t v___x_1668_; 
v___x_1666_ = lean_uint8_to_uint32(v___y_1665_);
v___x_1667_ = 32;
v___x_1668_ = lean_uint32_dec_eq(v___x_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
uint32_t v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = 9;
v___x_1670_ = lean_uint32_dec_eq(v___x_1666_, v___x_1669_);
return v___x_1670_;
}
else
{
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_1671_){
_start:
{
uint8_t v___y_3721__boxed_1672_; uint8_t v_res_1673_; lean_object* v_r_1674_; 
v___y_3721__boxed_1672_ = lean_unbox(v___y_1671_);
v_res_1673_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_3721__boxed_1672_);
v_r_1674_ = lean_box(v_res_1673_);
return v_r_1674_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(uint8_t v___y_1675_){
_start:
{
uint32_t v___x_1676_; uint32_t v___x_1682_; uint8_t v___x_1683_; 
v___x_1676_ = lean_uint8_to_uint32(v___y_1675_);
v___x_1682_ = 33;
v___x_1683_ = lean_uint32_dec_le(v___x_1682_, v___x_1676_);
if (v___x_1683_ == 0)
{
goto v___jp_1677_;
}
else
{
uint32_t v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = 126;
v___x_1685_ = lean_uint32_dec_le(v___x_1676_, v___x_1684_);
if (v___x_1685_ == 0)
{
goto v___jp_1677_;
}
else
{
return v___x_1685_;
}
}
v___jp_1677_:
{
uint32_t v___x_1678_; uint8_t v___x_1679_; 
v___x_1678_ = 32;
v___x_1679_ = lean_uint32_dec_eq(v___x_1676_, v___x_1678_);
if (v___x_1679_ == 0)
{
uint32_t v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = 9;
v___x_1681_ = lean_uint32_dec_eq(v___x_1676_, v___x_1680_);
return v___x_1681_;
}
else
{
return v___x_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed(lean_object* v___y_1686_){
_start:
{
uint8_t v___y_3734__boxed_1687_; uint8_t v_res_1688_; lean_object* v_r_1689_; 
v___y_3734__boxed_1687_ = lean_unbox(v___y_1686_);
v_res_1688_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(v___y_3734__boxed_1687_);
v_r_1689_ = lean_box(v_res_1688_);
return v_r_1689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_1690_, lean_object* v_pos_1691_){
_start:
{
lean_object* v_str_1692_; lean_object* v_startInclusive_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v_decide_1697_; 
v_str_1692_ = lean_ctor_get(v_s_1690_, 0);
v_startInclusive_1693_ = lean_ctor_get(v_s_1690_, 1);
v___x_1694_ = lean_nat_add(v_startInclusive_1693_, v_pos_1691_);
v___x_1695_ = lean_nat_sub(v___x_1694_, v_startInclusive_1693_);
v___x_1696_ = lean_unsigned_to_nat(0u);
v_decide_1697_ = lean_nat_dec_eq(v___x_1695_, v___x_1696_);
if (v_decide_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1706_; uint32_t v___x_1707_; uint32_t v___x_1708_; uint8_t v___x_1709_; 
lean_inc(v_startInclusive_1693_);
lean_inc_ref(v_str_1692_);
v___x_1698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1698_, 0, v_str_1692_);
lean_ctor_set(v___x_1698_, 1, v_startInclusive_1693_);
lean_ctor_set(v___x_1698_, 2, v___x_1694_);
v___x_1699_ = lean_unsigned_to_nat(1u);
v___x_1700_ = lean_nat_sub(v___x_1695_, v___x_1699_);
lean_dec(v___x_1695_);
v___x_1701_ = l_String_Slice_posLE(v___x_1698_, v___x_1700_);
lean_dec_ref_known(v___x_1698_, 3);
v___x_1706_ = lean_nat_add(v_startInclusive_1693_, v___x_1701_);
v___x_1707_ = lean_string_utf8_get_fast(v_str_1692_, v___x_1706_);
lean_dec(v___x_1706_);
v___x_1708_ = 32;
v___x_1709_ = lean_uint32_dec_eq(v___x_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
uint32_t v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = 9;
v___x_1711_ = lean_uint32_dec_eq(v___x_1707_, v___x_1710_);
if (v___x_1711_ == 0)
{
uint32_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = 13;
v___x_1713_ = lean_uint32_dec_eq(v___x_1707_, v___x_1712_);
if (v___x_1713_ == 0)
{
uint32_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = 10;
v___x_1715_ = lean_uint32_dec_eq(v___x_1707_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_dec(v___x_1701_);
return v_pos_1691_;
}
else
{
goto v___jp_1702_;
}
}
else
{
goto v___jp_1702_;
}
}
else
{
goto v___jp_1702_;
}
}
else
{
goto v___jp_1702_;
}
v___jp_1702_:
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = lean_nat_add(v___x_1701_, v___x_1699_);
v___x_1704_ = lean_nat_dec_le(v___x_1703_, v_pos_1691_);
lean_dec(v___x_1703_);
if (v___x_1704_ == 0)
{
lean_dec(v___x_1701_);
return v_pos_1691_;
}
else
{
lean_dec(v_pos_1691_);
v_pos_1691_ = v___x_1701_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1695_);
lean_dec(v___x_1694_);
return v_pos_1691_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_1716_, lean_object* v_pos_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_1716_, v_pos_1717_);
lean_dec_ref(v_s_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_pos_1727_; lean_object* v_pos_1731_; lean_object* v_maxHeaderNameLength_1734_; lean_object* v_maxHeaderValueLength_1735_; lean_object* v_maxSpaceSequence_1736_; lean_object* v___f_1737_; lean_object* v___x_1738_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1798_; lean_object* v_pos_1799_; lean_object* v_res_1800_; lean_object* v___x_1806_; lean_object* v_snd_1807_; lean_object* v_snd_1808_; uint8_t v___x_1809_; 
v_maxHeaderNameLength_1734_ = lean_ctor_get(v_limits_1724_, 6);
v_maxHeaderValueLength_1735_ = lean_ctor_get(v_limits_1724_, 7);
v_maxSpaceSequence_1736_ = lean_ctor_get(v_limits_1724_, 8);
v___f_1737_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1738_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1725_);
v___x_1806_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1737_, v_maxHeaderNameLength_1734_, v___x_1738_, v_a_1725_);
v_snd_1807_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_snd_1807_);
v_snd_1808_ = lean_ctor_get(v_snd_1807_, 1);
v___x_1809_ = lean_unbox(v_snd_1808_);
if (v___x_1809_ == 0)
{
lean_object* v_fst_1810_; lean_object* v_fst_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1969_; 
v_fst_1810_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_fst_1810_);
lean_dec_ref(v___x_1806_);
v_fst_1811_ = lean_ctor_get(v_snd_1807_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_snd_1807_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v_snd_1807_, 1);
lean_dec(v_unused_1970_);
v___x_1813_ = v_snd_1807_;
v_isShared_1814_ = v_isSharedCheck_1969_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_fst_1811_);
lean_dec(v_snd_1807_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1969_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_nat_dec_eq(v_fst_1810_, v___x_1738_);
if (v___x_1815_ == 0)
{
lean_object* v_array_1816_; lean_object* v_idx_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1964_; 
v_array_1816_ = lean_ctor_get(v_a_1725_, 0);
v_idx_1817_ = lean_ctor_get(v_a_1725_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_a_1725_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1819_ = v_a_1725_;
v_isShared_1820_ = v_isSharedCheck_1964_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_idx_1817_);
lean_inc(v_array_1816_);
lean_dec(v_a_1725_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1964_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___f_1821_; lean_object* v___y_1823_; lean_object* v_pos_1824_; lean_object* v_res_1825_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v_lower_1855_; lean_object* v_upper_1856_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___f_1867_; lean_object* v___y_1869_; lean_object* v_pos_1870_; lean_object* v___y_1897_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___y_1955_; uint8_t v___x_1963_; 
v___f_1821_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___f_1867_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_1952_ = lean_nat_add(v_idx_1817_, v_fst_1810_);
lean_dec(v_fst_1810_);
v___x_1953_ = lean_byte_array_size(v_array_1816_);
v___x_1963_ = lean_nat_dec_le(v_idx_1817_, v___x_1738_);
if (v___x_1963_ == 0)
{
v___y_1955_ = v_idx_1817_;
goto v___jp_1954_;
}
else
{
lean_dec(v_idx_1817_);
v___y_1955_ = v___x_1738_;
goto v___jp_1954_;
}
v___jp_1822_:
{
lean_object* v___x_1826_; lean_object* v_snd_1827_; lean_object* v_snd_1828_; uint8_t v___x_1829_; 
v___x_1826_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1821_, v_maxSpaceSequence_1736_, v___x_1738_, v_pos_1824_);
v_snd_1827_ = lean_ctor_get(v___x_1826_, 1);
lean_inc(v_snd_1827_);
lean_dec_ref(v___x_1826_);
v_snd_1828_ = lean_ctor_get(v_snd_1827_, 1);
v___x_1829_ = lean_unbox(v_snd_1828_);
if (v___x_1829_ == 0)
{
lean_object* v_fst_1830_; lean_object* v_array_1831_; lean_object* v_idx_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_fst_1830_ = lean_ctor_get(v_snd_1827_, 0);
lean_inc(v_fst_1830_);
lean_dec(v_snd_1827_);
v_array_1831_ = lean_ctor_get(v_fst_1830_, 0);
v_idx_1832_ = lean_ctor_get(v_fst_1830_, 1);
v___x_1833_ = lean_byte_array_size(v_array_1831_);
v___x_1834_ = lean_nat_dec_lt(v_idx_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
v___y_1798_ = v___y_1823_;
v_pos_1799_ = v_fst_1830_;
v_res_1800_ = v_res_1825_;
goto v___jp_1797_;
}
else
{
uint8_t v___x_1835_; uint32_t v___x_1836_; uint32_t v___x_1837_; uint8_t v___x_1838_; 
v___x_1835_ = lean_byte_array_fget(v_array_1831_, v_idx_1832_);
v___x_1836_ = lean_uint8_to_uint32(v___x_1835_);
v___x_1837_ = 32;
v___x_1838_ = lean_uint32_dec_eq(v___x_1836_, v___x_1837_);
if (v___x_1838_ == 0)
{
uint32_t v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = 9;
v___x_1840_ = lean_uint32_dec_eq(v___x_1836_, v___x_1839_);
if (v___x_1840_ == 0)
{
v___y_1798_ = v___y_1823_;
v_pos_1799_ = v_fst_1830_;
v_res_1800_ = v_res_1825_;
goto v___jp_1797_;
}
else
{
lean_dec(v_res_1825_);
lean_dec_ref(v___y_1823_);
v_pos_1731_ = v_fst_1830_;
goto v___jp_1730_;
}
}
else
{
lean_dec(v_res_1825_);
lean_dec_ref(v___y_1823_);
v_pos_1731_ = v_fst_1830_;
goto v___jp_1730_;
}
}
}
else
{
lean_object* v_fst_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_res_1825_);
lean_dec_ref(v___y_1823_);
v_fst_1841_ = lean_ctor_get(v_snd_1827_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_snd_1827_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v_snd_1827_, 1);
lean_dec(v_unused_1850_);
v___x_1843_ = v_snd_1827_;
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_fst_1841_);
lean_dec(v_snd_1827_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1845_ = lean_box(0);
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 1);
lean_ctor_set(v___x_1843_, 1, v___x_1845_);
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_fst_1841_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
v___jp_1851_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = l_ByteArray_toByteSlice(v___y_1854_, v_lower_1855_, v_upper_1856_);
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
v___y_1823_ = v___y_1852_;
v_pos_1824_ = v___y_1853_;
v_res_1825_ = v___x_1858_;
goto v___jp_1822_;
}
v___jp_1859_:
{
uint8_t v___x_1866_; 
v___x_1866_ = lean_nat_dec_le(v___y_1860_, v___y_1861_);
if (v___x_1866_ == 0)
{
lean_dec(v___y_1860_);
v___y_1852_ = v___y_1863_;
v___y_1853_ = v___y_1862_;
v___y_1854_ = v___y_1864_;
v_lower_1855_ = v___y_1865_;
v_upper_1856_ = v___y_1861_;
goto v___jp_1851_;
}
else
{
lean_dec(v___y_1861_);
v___y_1852_ = v___y_1863_;
v___y_1853_ = v___y_1862_;
v___y_1854_ = v___y_1864_;
v_lower_1855_ = v___y_1865_;
v_upper_1856_ = v___y_1860_;
goto v___jp_1851_;
}
}
v___jp_1868_:
{
lean_object* v___x_1871_; lean_object* v_snd_1872_; lean_object* v_snd_1873_; uint8_t v___x_1874_; 
lean_inc_ref(v_pos_1870_);
v___x_1871_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1867_, v_maxHeaderValueLength_1735_, v___x_1738_, v_pos_1870_);
v_snd_1872_ = lean_ctor_get(v___x_1871_, 1);
lean_inc(v_snd_1872_);
v_snd_1873_ = lean_ctor_get(v_snd_1872_, 1);
v___x_1874_ = lean_unbox(v_snd_1873_);
if (v___x_1874_ == 0)
{
lean_object* v_fst_1875_; lean_object* v_fst_1876_; lean_object* v_array_1877_; lean_object* v_idx_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_fst_1875_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_fst_1875_);
lean_dec_ref(v___x_1871_);
v_fst_1876_ = lean_ctor_get(v_snd_1872_, 0);
lean_inc(v_fst_1876_);
lean_dec(v_snd_1872_);
v_array_1877_ = lean_ctor_get(v_pos_1870_, 0);
lean_inc_ref(v_array_1877_);
v_idx_1878_ = lean_ctor_get(v_pos_1870_, 1);
lean_inc(v_idx_1878_);
lean_dec_ref(v_pos_1870_);
v___x_1879_ = lean_nat_add(v_idx_1878_, v_fst_1875_);
lean_dec(v_fst_1875_);
v___x_1880_ = lean_byte_array_size(v_array_1877_);
v___x_1881_ = lean_nat_dec_le(v_idx_1878_, v___x_1738_);
if (v___x_1881_ == 0)
{
v___y_1860_ = v___x_1879_;
v___y_1861_ = v___x_1880_;
v___y_1862_ = v_fst_1876_;
v___y_1863_ = v___y_1869_;
v___y_1864_ = v_array_1877_;
v___y_1865_ = v_idx_1878_;
goto v___jp_1859_;
}
else
{
lean_dec(v_idx_1878_);
v___y_1860_ = v___x_1879_;
v___y_1861_ = v___x_1880_;
v___y_1862_ = v_fst_1876_;
v___y_1863_ = v___y_1869_;
v___y_1864_ = v_array_1877_;
v___y_1865_ = v___x_1738_;
goto v___jp_1859_;
}
}
else
{
lean_object* v_fst_1882_; lean_object* v_idx_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v___x_1871_);
v_fst_1882_ = lean_ctor_get(v_snd_1872_, 0);
lean_inc(v_fst_1882_);
lean_dec(v_snd_1872_);
v_idx_1883_ = lean_ctor_get(v_pos_1870_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_pos_1870_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v_pos_1870_, 0);
lean_dec(v_unused_1895_);
v___x_1885_ = v_pos_1870_;
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_idx_1883_);
lean_dec(v_pos_1870_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_idx_1887_; uint8_t v___x_1888_; 
v_idx_1887_ = lean_ctor_get(v_fst_1882_, 1);
v___x_1888_ = lean_nat_dec_eq(v_idx_1883_, v_idx_1887_);
lean_dec(v_idx_1883_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_dec_ref(v___y_1869_);
v___x_1889_ = lean_box(0);
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 1);
lean_ctor_set(v___x_1885_, 1, v___x_1889_);
lean_ctor_set(v___x_1885_, 0, v_fst_1882_);
v___x_1891_ = v___x_1885_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_fst_1882_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
else
{
lean_object* v___x_1893_; 
lean_del_object(v___x_1885_);
v___x_1893_ = lean_box(0);
v___y_1823_ = v___y_1869_;
v_pos_1824_ = v_fst_1882_;
v_res_1825_ = v___x_1893_;
goto v___jp_1822_;
}
}
}
}
v___jp_1896_:
{
lean_object* v_array_1898_; lean_object* v_idx_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v_array_1898_ = lean_ctor_get(v_fst_1811_, 0);
v_idx_1899_ = lean_ctor_get(v_fst_1811_, 1);
v___x_1900_ = lean_byte_array_size(v_array_1898_);
v___x_1901_ = lean_nat_dec_lt(v_idx_1899_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
lean_dec_ref(v___y_1897_);
lean_dec_ref(v_array_1816_);
v___x_1902_ = lean_box(0);
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 1);
lean_ctor_set(v___x_1819_, 1, v___x_1902_);
lean_ctor_set(v___x_1819_, 0, v_fst_1811_);
v___x_1904_ = v___x_1819_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_fst_1811_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
uint8_t v___x_1906_; uint8_t v_got_1907_; uint8_t v___x_1908_; 
v___x_1906_ = 58;
v_got_1907_ = lean_byte_array_fget(v_array_1898_, v_idx_1899_);
v___x_1908_ = lean_uint8_dec_eq(v_got_1907_, v___x_1906_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec_ref(v___y_1897_);
lean_dec_ref(v_array_1816_);
v___x_1909_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 1);
lean_ctor_set(v___x_1819_, 1, v___x_1909_);
lean_ctor_set(v___x_1819_, 0, v_fst_1811_);
v___x_1911_ = v___x_1819_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_fst_1811_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1949_; 
lean_inc(v_idx_1899_);
lean_inc_ref(v_array_1898_);
lean_del_object(v___x_1819_);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_fst_1811_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; lean_object* v_unused_1951_; 
v_unused_1950_ = lean_ctor_get(v_fst_1811_, 1);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_fst_1811_, 0);
lean_dec(v_unused_1951_);
v___x_1914_ = v_fst_1811_;
v_isShared_1915_ = v_isSharedCheck_1949_;
goto v_resetjp_1913_;
}
else
{
lean_dec(v_fst_1811_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1949_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1916_ = lean_unsigned_to_nat(1u);
v___x_1917_ = lean_nat_add(v_idx_1899_, v___x_1916_);
lean_dec(v_idx_1899_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___x_1917_);
v___x_1919_ = v___x_1914_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_array_1898_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; lean_object* v_snd_1921_; lean_object* v_snd_1922_; uint8_t v___x_1923_; 
v___x_1920_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1821_, v_maxSpaceSequence_1736_, v___x_1738_, v___x_1919_);
v_snd_1921_ = lean_ctor_get(v___x_1920_, 1);
lean_inc(v_snd_1921_);
lean_dec_ref(v___x_1920_);
v_snd_1922_ = lean_ctor_get(v_snd_1921_, 1);
v___x_1923_ = lean_unbox(v_snd_1922_);
if (v___x_1923_ == 0)
{
lean_object* v_fst_1924_; lean_object* v_array_1925_; lean_object* v_idx_1926_; lean_object* v_lower_1927_; lean_object* v_upper_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_fst_1924_ = lean_ctor_get(v_snd_1921_, 0);
lean_inc(v_fst_1924_);
lean_dec(v_snd_1921_);
v_array_1925_ = lean_ctor_get(v_fst_1924_, 0);
v_idx_1926_ = lean_ctor_get(v_fst_1924_, 1);
v_lower_1927_ = lean_ctor_get(v___y_1897_, 0);
lean_inc(v_lower_1927_);
v_upper_1928_ = lean_ctor_get(v___y_1897_, 1);
lean_inc(v_upper_1928_);
lean_dec_ref(v___y_1897_);
v___x_1929_ = l_ByteArray_toByteSlice(v_array_1816_, v_lower_1927_, v_upper_1928_);
v___x_1930_ = lean_byte_array_size(v_array_1925_);
v___x_1931_ = lean_nat_dec_lt(v_idx_1926_, v___x_1930_);
if (v___x_1931_ == 0)
{
v___y_1869_ = v___x_1929_;
v_pos_1870_ = v_fst_1924_;
goto v___jp_1868_;
}
else
{
uint8_t v___x_1932_; uint32_t v___x_1933_; uint32_t v___x_1934_; uint8_t v___x_1935_; 
v___x_1932_ = lean_byte_array_fget(v_array_1925_, v_idx_1926_);
v___x_1933_ = lean_uint8_to_uint32(v___x_1932_);
v___x_1934_ = 32;
v___x_1935_ = lean_uint32_dec_eq(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
uint32_t v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = 9;
v___x_1937_ = lean_uint32_dec_eq(v___x_1933_, v___x_1936_);
if (v___x_1937_ == 0)
{
v___y_1869_ = v___x_1929_;
v_pos_1870_ = v_fst_1924_;
goto v___jp_1868_;
}
else
{
lean_dec_ref(v___x_1929_);
v_pos_1727_ = v_fst_1924_;
goto v___jp_1726_;
}
}
else
{
lean_dec_ref(v___x_1929_);
v_pos_1727_ = v_fst_1924_;
goto v___jp_1726_;
}
}
}
else
{
lean_object* v_fst_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v___y_1897_);
lean_dec_ref(v_array_1816_);
v_fst_1938_ = lean_ctor_get(v_snd_1921_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_snd_1921_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v_snd_1921_, 1);
lean_dec(v_unused_1947_);
v___x_1940_ = v_snd_1921_;
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_fst_1938_);
lean_dec(v_snd_1921_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_box(0);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 1);
lean_ctor_set(v___x_1940_, 1, v___x_1942_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_fst_1938_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
}
}
}
v___jp_1954_:
{
uint8_t v___x_1956_; 
v___x_1956_ = lean_nat_dec_le(v___x_1952_, v___x_1953_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1958_; 
lean_dec(v___x_1952_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1953_);
lean_ctor_set(v___x_1813_, 0, v___y_1955_);
v___x_1958_ = v___x_1813_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___y_1955_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
v___y_1897_ = v___x_1958_;
goto v___jp_1896_;
}
}
else
{
lean_object* v___x_1961_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1952_);
lean_ctor_set(v___x_1813_, 0, v___y_1955_);
v___x_1961_ = v___x_1813_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___y_1955_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___x_1952_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
v___y_1897_ = v___x_1961_;
goto v___jp_1896_;
}
}
}
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
lean_dec(v_fst_1811_);
lean_dec(v_fst_1810_);
v___x_1965_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1814_ == 0)
{
lean_ctor_set_tag(v___x_1813_, 1);
lean_ctor_set(v___x_1813_, 1, v___x_1965_);
lean_ctor_set(v___x_1813_, 0, v_a_1725_);
v___x_1967_ = v___x_1813_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1725_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_fst_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v___x_1806_);
lean_dec_ref(v_a_1725_);
v_fst_1971_ = lean_ctor_get(v_snd_1807_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_snd_1807_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v_snd_1807_, 1);
lean_dec(v_unused_1980_);
v___x_1973_ = v_snd_1807_;
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_fst_1971_);
lean_dec(v_snd_1807_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = lean_box(0);
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 1);
lean_ctor_set(v___x_1973_, 1, v___x_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_fst_1971_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
v___jp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_pos_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
return v___x_1729_;
}
v___jp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_pos_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
return v___x_1733_;
}
v___jp_1739_:
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_1742_, v___y_1741_);
lean_dec(v___y_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_pos_1744_; lean_object* v_res_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1758_; 
v_pos_1744_ = lean_ctor_get(v___x_1743_, 0);
v_res_1745_ = lean_ctor_get(v___x_1743_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1747_ = v___x_1743_;
v_isShared_1748_ = v_isSharedCheck_1758_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_res_1745_);
lean_inc(v_pos_1744_);
lean_dec(v___x_1743_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1758_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1749_ = lean_string_utf8_byte_size(v_res_1745_);
lean_inc(v_res_1745_);
v___x_1750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1750_, 0, v_res_1745_);
lean_ctor_set(v___x_1750_, 1, v___x_1738_);
lean_ctor_set(v___x_1750_, 2, v___x_1749_);
v___x_1751_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_1750_, v___x_1749_);
lean_dec_ref_known(v___x_1750_, 3);
v___x_1752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1752_, 0, v_res_1745_);
lean_ctor_set(v___x_1752_, 1, v___x_1738_);
lean_ctor_set(v___x_1752_, 2, v___x_1751_);
v___x_1753_ = l_String_Slice_toString(v___x_1752_);
lean_dec_ref_known(v___x_1752_, 3);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___y_1740_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v___x_1754_);
v___x_1756_ = v___x_1747_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_pos_1744_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v_pos_1759_; lean_object* v_err_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v___y_1740_);
v_pos_1759_ = lean_ctor_get(v___x_1743_, 0);
v_err_1760_ = lean_ctor_get(v___x_1743_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1743_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_err_1760_);
lean_inc(v_pos_1759_);
lean_dec(v___x_1743_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_pos_1759_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_err_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
v___jp_1768_:
{
uint8_t v___x_1772_; 
v___x_1772_ = lean_string_validate_utf8(v___y_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_dec_ref(v___y_1771_);
v___x_1773_ = lean_box(0);
v___y_1740_ = v___y_1769_;
v___y_1741_ = v___y_1770_;
v___y_1742_ = v___x_1773_;
goto v___jp_1739_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_string_from_utf8_unchecked(v___y_1771_);
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
v___y_1740_ = v___y_1769_;
v___y_1741_ = v___y_1770_;
v___y_1742_ = v___x_1775_;
goto v___jp_1739_;
}
}
v___jp_1776_:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_1779_, v___y_1778_);
lean_dec(v___y_1779_);
if (lean_obj_tag(v___x_1780_) == 0)
{
if (lean_obj_tag(v___y_1777_) == 0)
{
lean_object* v_pos_1781_; lean_object* v_res_1782_; lean_object* v___x_1783_; 
v_pos_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_pos_1781_);
v_res_1782_ = lean_ctor_get(v___x_1780_, 1);
lean_inc(v_res_1782_);
lean_dec_ref_known(v___x_1780_, 2);
v___x_1783_ = l_ByteArray_empty;
v___y_1769_ = v_res_1782_;
v___y_1770_ = v_pos_1781_;
v___y_1771_ = v___x_1783_;
goto v___jp_1768_;
}
else
{
lean_object* v_pos_1784_; lean_object* v_res_1785_; lean_object* v_val_1786_; lean_object* v___x_1787_; 
v_pos_1784_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_pos_1784_);
v_res_1785_ = lean_ctor_get(v___x_1780_, 1);
lean_inc(v_res_1785_);
lean_dec_ref_known(v___x_1780_, 2);
v_val_1786_ = lean_ctor_get(v___y_1777_, 0);
lean_inc(v_val_1786_);
lean_dec_ref_known(v___y_1777_, 1);
v___x_1787_ = l_ByteSlice_toByteArray(v_val_1786_);
v___y_1769_ = v_res_1785_;
v___y_1770_ = v_pos_1784_;
v___y_1771_ = v___x_1787_;
goto v___jp_1768_;
}
}
else
{
lean_object* v_pos_1788_; lean_object* v_err_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v___y_1777_);
v_pos_1788_ = lean_ctor_get(v___x_1780_, 0);
v_err_1789_ = lean_ctor_get(v___x_1780_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1780_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_err_1789_);
lean_inc(v_pos_1788_);
lean_dec(v___x_1780_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_pos_1788_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_err_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
v___jp_1797_:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = l_ByteSlice_toByteArray(v___y_1798_);
v___x_1802_ = lean_string_validate_utf8(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
lean_dec_ref(v___x_1801_);
v___x_1803_ = lean_box(0);
v___y_1777_ = v_res_1800_;
v___y_1778_ = v_pos_1799_;
v___y_1779_ = v___x_1803_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_string_from_utf8_unchecked(v___x_1801_);
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
v___y_1777_ = v_res_1800_;
v___y_1778_ = v_pos_1799_;
v___y_1779_ = v___x_1805_;
goto v___jp_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_1981_, v_a_1982_);
lean_dec_ref(v_limits_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
if (lean_obj_tag(v_x_1985_) == 0)
{
uint8_t v___x_1986_; 
v___x_1986_ = 1;
return v___x_1986_;
}
else
{
uint8_t v___x_1987_; 
v___x_1987_ = 0;
return v___x_1987_;
}
}
else
{
if (lean_obj_tag(v_x_1985_) == 0)
{
uint8_t v___x_1988_; 
v___x_1988_ = 0;
return v___x_1988_;
}
else
{
lean_object* v_val_1989_; lean_object* v_val_1990_; uint8_t v___x_1991_; uint8_t v___x_1992_; uint8_t v___x_1993_; 
v_val_1989_ = lean_ctor_get(v_x_1984_, 0);
v_val_1990_ = lean_ctor_get(v_x_1985_, 0);
v___x_1991_ = lean_unbox(v_val_1989_);
v___x_1992_ = lean_unbox(v_val_1990_);
v___x_1993_ = lean_uint8_dec_eq(v___x_1991_, v___x_1992_);
return v___x_1993_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
uint8_t v_res_1996_; lean_object* v_r_1997_; 
v_res_1996_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_1994_, v_x_1995_);
lean_dec(v_x_1995_);
lean_dec(v_x_1994_);
v_r_1997_ = lean_box(v_res_1996_);
return v_r_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___y_2007_; lean_object* v_pos_2030_; lean_object* v_res_2031_; lean_object* v_array_2069_; lean_object* v_idx_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_array_2069_ = lean_ctor_get(v_a_2005_, 0);
v_idx_2070_ = lean_ctor_get(v_a_2005_, 1);
v___x_2071_ = lean_byte_array_size(v_array_2069_);
v___x_2072_ = lean_nat_dec_lt(v_idx_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_box(0);
v_pos_2030_ = v_a_2005_;
v_res_2031_ = v___x_2073_;
goto v___jp_2029_;
}
else
{
uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_byte_array_fget(v_array_2069_, v_idx_2070_);
v___x_2075_ = lean_box(v___x_2074_);
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
v_pos_2030_ = v_a_2005_;
v_res_2031_ = v___x_2076_;
goto v___jp_2029_;
}
v___jp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2009_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2008_, v___y_2007_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_pos_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
v_pos_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_2009_, 1);
lean_dec(v_unused_2019_);
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_pos_2010_);
lean_dec(v___x_2009_);
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
lean_ctor_set(v___x_2012_, 1, v___x_2014_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_pos_2010_);
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
else
{
lean_object* v_pos_2020_; lean_object* v_err_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
v_pos_2020_ = lean_ctor_get(v___x_2009_, 0);
v_err_2021_ = lean_ctor_get(v___x_2009_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2009_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_err_2021_);
lean_inc(v_pos_2020_);
lean_dec(v___x_2009_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_pos_2020_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_err_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
v___jp_2029_:
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_2033_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_2035_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2031_, v___x_2034_);
lean_dec(v_res_2031_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2004_, v_pos_2030_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_pos_2037_; lean_object* v_res_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_pos_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_pos_2037_);
v_res_2038_ = lean_ctor_get(v___x_2036_, 1);
lean_inc(v_res_2038_);
lean_dec_ref_known(v___x_2036_, 2);
v___x_2039_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2040_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2039_, v_pos_2037_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_pos_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2049_; 
v_pos_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2040_, 1);
lean_dec(v_unused_2050_);
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_pos_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2049_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_res_2038_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v___x_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_pos_2041_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
else
{
lean_object* v_pos_2051_; lean_object* v_err_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_res_2038_);
v_pos_2051_ = lean_ctor_get(v___x_2040_, 0);
v_err_2052_ = lean_ctor_get(v___x_2040_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2040_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_err_2052_);
lean_inc(v_pos_2051_);
lean_dec(v___x_2040_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_pos_2051_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_err_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_pos_2060_; lean_object* v_err_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_pos_2060_ = lean_ctor_get(v___x_2036_, 0);
v_err_2061_ = lean_ctor_get(v___x_2036_, 1);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2036_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_err_2061_);
lean_inc(v_pos_2060_);
lean_dec(v___x_2036_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_pos_2060_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_err_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
v___y_2007_ = v_pos_2030_;
goto v___jp_2006_;
}
}
else
{
lean_dec(v_res_2031_);
v___y_2007_ = v_pos_2030_;
goto v___jp_2006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2077_, v_a_2078_);
lean_dec_ref(v_limits_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2084_){
_start:
{
lean_object* v_array_2085_; lean_object* v_idx_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v_array_2085_ = lean_ctor_get(v_a_2084_, 0);
v_idx_2086_ = lean_ctor_get(v_a_2084_, 1);
v___x_2087_ = lean_byte_array_size(v_array_2085_);
v___x_2088_ = lean_nat_dec_lt(v_idx_2086_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v_a_2084_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
return v___x_2090_;
}
else
{
uint8_t v___x_2091_; uint8_t v_got_2092_; uint8_t v___x_2093_; 
v___x_2091_ = 92;
v_got_2092_ = lean_byte_array_fget(v_array_2085_, v_idx_2086_);
v___x_2093_ = lean_uint8_dec_eq(v_got_2092_, v___x_2091_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_a_2084_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
return v___x_2095_;
}
else
{
lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2129_; 
lean_inc(v_idx_2086_);
lean_inc_ref(v_array_2085_);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_a_2084_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; 
v_unused_2130_ = lean_ctor_get(v_a_2084_, 1);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_a_2084_, 0);
lean_dec(v_unused_2131_);
v___x_2097_ = v_a_2084_;
v_isShared_2098_ = v_isSharedCheck_2129_;
goto v_resetjp_2096_;
}
else
{
lean_dec(v_a_2084_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2129_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_add(v_idx_2086_, v___x_2099_);
lean_dec(v_idx_2086_);
v___x_2101_ = lean_nat_dec_lt(v___x_2100_, v___x_2087_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2103_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2100_);
v___x_2103_ = v___x_2097_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_array_2085_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2100_);
v___x_2103_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
return v___x_2105_;
}
}
else
{
uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2107_ = lean_byte_array_fget(v_array_2085_, v___x_2100_);
v___x_2108_ = lean_nat_add(v___x_2100_, v___x_2099_);
lean_dec(v___x_2100_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2108_);
v___x_2110_ = v___x_2097_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_array_2085_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint32_t v___x_2113_; uint32_t v___x_2120_; uint8_t v___x_2121_; 
v___x_2111_ = lean_box(v___x_2107_);
lean_inc_ref(v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_uint8_to_uint32(v___x_2107_);
v___x_2120_ = 9;
v___x_2121_ = lean_uint32_dec_eq(v___x_2113_, v___x_2120_);
if (v___x_2121_ == 0)
{
uint32_t v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = 32;
v___x_2123_ = lean_uint32_dec_eq(v___x_2113_, v___x_2122_);
if (v___x_2123_ == 0)
{
uint32_t v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = 33;
v___x_2125_ = lean_uint32_dec_le(v___x_2124_, v___x_2113_);
if (v___x_2125_ == 0)
{
lean_dec_ref_known(v___x_2112_, 2);
goto v___jp_2114_;
}
else
{
uint32_t v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = 126;
v___x_2127_ = lean_uint32_dec_le(v___x_2113_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_dec_ref_known(v___x_2112_, 2);
goto v___jp_2114_;
}
else
{
lean_dec_ref(v___x_2110_);
return v___x_2112_;
}
}
}
else
{
lean_dec_ref(v___x_2110_);
return v___x_2112_;
}
}
else
{
lean_dec_ref(v___x_2110_);
return v___x_2112_;
}
v___jp_2114_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2115_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2116_ = l_Char_quote(v___x_2113_);
v___x_2117_ = lean_string_append(v___x_2115_, v___x_2116_);
lean_dec_ref(v___x_2116_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2110_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
return v___x_2119_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2136_, lean_object* v_buf_2137_, lean_object* v_length_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_array_2140_; lean_object* v_idx_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v_array_2140_ = lean_ctor_get(v_a_2139_, 0);
v_idx_2141_ = lean_ctor_get(v_a_2139_, 1);
v___x_2142_ = lean_byte_array_size(v_array_2140_);
v___x_2143_ = lean_nat_dec_lt(v_idx_2141_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec(v_length_2138_);
lean_dec_ref(v_buf_2137_);
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_a_2139_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
return v___x_2145_;
}
else
{
lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2218_; 
lean_inc(v_idx_2141_);
lean_inc_ref(v_array_2140_);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_a_2139_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; lean_object* v_unused_2220_; 
v_unused_2219_ = lean_ctor_get(v_a_2139_, 1);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_a_2139_, 0);
lean_dec(v_unused_2220_);
v___x_2147_ = v_a_2139_;
v_isShared_2148_ = v_isSharedCheck_2218_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v_a_2139_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2218_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
uint8_t v_c_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_it_x27_2153_; 
v_c_2149_ = lean_byte_array_fget(v_array_2140_, v_idx_2141_);
v___x_2150_ = lean_unsigned_to_nat(1u);
v___x_2151_ = lean_nat_add(v_idx_2141_, v___x_2150_);
lean_dec(v_idx_2141_);
lean_inc(v___x_2151_);
lean_inc_ref(v_array_2140_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 1, v___x_2151_);
v_it_x27_2153_ = v___x_2147_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_array_2140_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2151_);
v_it_x27_2153_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
uint8_t v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = 34;
v___x_2169_ = lean_uint8_dec_eq(v_c_2149_, v___x_2168_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = 92;
v___x_2171_ = lean_uint8_dec_eq(v_c_2149_, v___x_2170_);
if (v___x_2171_ == 0)
{
uint32_t v___x_2172_; uint32_t v___x_2178_; uint8_t v___x_2179_; 
lean_dec(v___x_2151_);
lean_dec_ref(v_array_2140_);
v___x_2172_ = lean_uint8_to_uint32(v_c_2149_);
v___x_2178_ = 9;
v___x_2179_ = lean_uint32_dec_eq(v___x_2172_, v___x_2178_);
if (v___x_2179_ == 0)
{
uint32_t v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = 32;
v___x_2181_ = lean_uint32_dec_eq(v___x_2172_, v___x_2180_);
if (v___x_2181_ == 0)
{
uint32_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = 33;
v___x_2183_ = lean_uint32_dec_eq(v___x_2172_, v___x_2182_);
if (v___x_2183_ == 0)
{
uint32_t v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = 35;
v___x_2185_ = lean_uint32_dec_le(v___x_2184_, v___x_2172_);
if (v___x_2185_ == 0)
{
goto v___jp_2173_;
}
else
{
uint32_t v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = 91;
v___x_2187_ = lean_uint32_dec_le(v___x_2172_, v___x_2186_);
if (v___x_2187_ == 0)
{
goto v___jp_2173_;
}
else
{
goto v___jp_2154_;
}
}
}
else
{
goto v___jp_2154_;
}
}
else
{
goto v___jp_2154_;
}
}
else
{
goto v___jp_2154_;
}
v___jp_2173_:
{
uint32_t v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = 93;
v___x_2175_ = lean_uint32_dec_le(v___x_2174_, v___x_2172_);
if (v___x_2175_ == 0)
{
lean_dec(v_length_2138_);
lean_dec_ref(v_buf_2137_);
goto v___jp_2161_;
}
else
{
uint32_t v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = 126;
v___x_2177_ = lean_uint32_dec_le(v___x_2172_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_dec(v_length_2138_);
lean_dec_ref(v_buf_2137_);
goto v___jp_2161_;
}
else
{
goto v___jp_2154_;
}
}
}
}
else
{
uint8_t v___x_2188_; 
v___x_2188_ = lean_nat_dec_lt(v___x_2151_, v___x_2142_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v___x_2151_);
lean_dec_ref(v_array_2140_);
lean_dec(v_length_2138_);
lean_dec_ref(v_buf_2137_);
v___x_2189_ = lean_box(0);
v___x_2190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_it_x27_2153_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
return v___x_2190_;
}
else
{
uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint32_t v___x_2201_; uint32_t v___x_2208_; uint8_t v___x_2209_; 
lean_dec_ref(v_it_x27_2153_);
v___x_2191_ = lean_byte_array_fget(v_array_2140_, v___x_2151_);
v___x_2192_ = lean_nat_add(v___x_2151_, v___x_2150_);
lean_dec(v___x_2151_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_array_2140_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2201_ = lean_uint8_to_uint32(v___x_2191_);
v___x_2208_ = 9;
v___x_2209_ = lean_uint32_dec_eq(v___x_2201_, v___x_2208_);
if (v___x_2209_ == 0)
{
uint32_t v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = 32;
v___x_2211_ = lean_uint32_dec_eq(v___x_2201_, v___x_2210_);
if (v___x_2211_ == 0)
{
uint32_t v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = 33;
v___x_2213_ = lean_uint32_dec_le(v___x_2212_, v___x_2201_);
if (v___x_2213_ == 0)
{
lean_dec(v_length_2138_);
lean_dec_ref(v_buf_2137_);
goto v___jp_2202_;
}
else
{
uint32_t v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = 126;
v___x_2215_ = lean_uint32_dec_le(v___x_2201_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_dec(v_length_2138_);
lean_dec_ref(v_buf_2137_);
goto v___jp_2202_;
}
else
{
goto v___jp_2194_;
}
}
}
else
{
goto v___jp_2194_;
}
}
else
{
goto v___jp_2194_;
}
v___jp_2194_:
{
lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = lean_nat_add(v_length_2138_, v___x_2150_);
lean_dec(v_length_2138_);
v___x_2196_ = lean_nat_dec_lt(v_maxLength_2136_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_byte_array_push(v_buf_2137_, v___x_2191_);
v_buf_2137_ = v___x_2197_;
v_length_2138_ = v___x_2195_;
v_a_2139_ = v___x_2193_;
goto _start;
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v___x_2195_);
lean_dec_ref(v_buf_2137_);
v___x_2199_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2193_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
return v___x_2200_;
}
}
v___jp_2202_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2203_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2204_ = l_Char_quote(v___x_2201_);
v___x_2205_ = lean_string_append(v___x_2203_, v___x_2204_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2193_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
return v___x_2207_;
}
}
}
}
else
{
lean_object* v___x_2216_; 
lean_dec(v___x_2151_);
lean_dec_ref(v_array_2140_);
lean_dec(v_length_2138_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_it_x27_2153_);
lean_ctor_set(v___x_2216_, 1, v_buf_2137_);
return v___x_2216_;
}
v___jp_2154_:
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = lean_nat_add(v_length_2138_, v___x_2150_);
lean_dec(v_length_2138_);
v___x_2156_ = lean_nat_dec_lt(v_maxLength_2136_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_byte_array_push(v_buf_2137_, v_c_2149_);
v_buf_2137_ = v___x_2157_;
v_length_2138_ = v___x_2155_;
v_a_2139_ = v_it_x27_2153_;
goto _start;
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v___x_2155_);
lean_dec_ref(v_buf_2137_);
v___x_2159_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2160_, 0, v_it_x27_2153_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
return v___x_2160_;
}
}
v___jp_2161_:
{
lean_object* v___x_2162_; uint32_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2162_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2163_ = lean_uint8_to_uint32(v_c_2149_);
v___x_2164_ = l_Char_quote(v___x_2163_);
v___x_2165_ = lean_string_append(v___x_2162_, v___x_2164_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
v___x_2167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2167_, 0, v_it_x27_2153_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
return v___x_2167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2221_, lean_object* v_buf_2222_, lean_object* v_length_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2221_, v_buf_2222_, v_length_2223_, v_a_2224_);
lean_dec(v_maxLength_2221_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_array_2231_; lean_object* v_idx_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v_array_2231_ = lean_ctor_get(v_a_2230_, 0);
v_idx_2232_ = lean_ctor_get(v_a_2230_, 1);
v___x_2233_ = lean_byte_array_size(v_array_2231_);
v___x_2234_ = lean_nat_dec_lt(v_idx_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2236_, 0, v_a_2230_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
return v___x_2236_;
}
else
{
uint8_t v___x_2237_; uint8_t v_got_2238_; uint8_t v___x_2239_; 
v___x_2237_ = 34;
v_got_2238_ = lean_byte_array_fget(v_array_2231_, v_idx_2232_);
v___x_2239_ = lean_uint8_dec_eq(v_got_2238_, v___x_2237_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_a_2230_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
return v___x_2241_;
}
else
{
lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2270_; 
lean_inc(v_idx_2232_);
lean_inc_ref(v_array_2231_);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_a_2230_);
if (v_isSharedCheck_2270_ == 0)
{
lean_object* v_unused_2271_; lean_object* v_unused_2272_; 
v_unused_2271_ = lean_ctor_get(v_a_2230_, 1);
lean_dec(v_unused_2271_);
v_unused_2272_ = lean_ctor_get(v_a_2230_, 0);
lean_dec(v_unused_2272_);
v___x_2243_ = v_a_2230_;
v_isShared_2244_ = v_isSharedCheck_2270_;
goto v_resetjp_2242_;
}
else
{
lean_dec(v_a_2230_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2270_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_idx_2232_, v___x_2245_);
lean_dec(v_idx_2232_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2246_);
v___x_2248_ = v___x_2243_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_array_2231_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = l_ByteArray_empty;
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2229_, v___x_2249_, v___x_2250_, v___x_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_pos_2252_; lean_object* v_res_2253_; uint8_t v___x_2254_; 
v_pos_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_pos_2252_);
v_res_2253_ = lean_ctor_get(v___x_2251_, 1);
lean_inc(v_res_2253_);
lean_dec_ref_known(v___x_2251_, 2);
v___x_2254_ = lean_string_validate_utf8(v_res_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec(v_res_2253_);
v___x_2255_ = lean_box(0);
v___x_2256_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2255_, v_pos_2252_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_string_from_utf8_unchecked(v_res_2253_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
v___x_2259_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2258_, v_pos_2252_);
lean_dec_ref_known(v___x_2258_, 1);
return v___x_2259_;
}
}
else
{
lean_object* v_pos_2260_; lean_object* v_err_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_pos_2260_ = lean_ctor_get(v___x_2251_, 0);
v_err_2261_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2251_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_err_2261_);
lean_inc(v_pos_2260_);
lean_dec(v___x_2251_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_pos_2260_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_err_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_2273_, v_a_2274_);
lean_dec(v_maxLength_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_2276_, lean_object* v_maxSpaceSequence_2277_, lean_object* v_x_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_pos_2281_; lean_object* v_pos_2285_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v_snd_2290_; lean_object* v_snd_2291_; uint8_t v___x_2292_; 
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2276_, v_maxSpaceSequence_2277_, v___x_2288_, v___y_2279_);
v_snd_2290_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_snd_2290_);
lean_dec_ref(v___x_2289_);
v_snd_2291_ = lean_ctor_get(v_snd_2290_, 1);
v___x_2292_ = lean_unbox(v_snd_2291_);
if (v___x_2292_ == 0)
{
lean_object* v_fst_2293_; lean_object* v_array_2294_; lean_object* v_idx_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v_fst_2293_ = lean_ctor_get(v_snd_2290_, 0);
lean_inc(v_fst_2293_);
lean_dec(v_snd_2290_);
v_array_2294_ = lean_ctor_get(v_fst_2293_, 0);
v_idx_2295_ = lean_ctor_get(v_fst_2293_, 1);
v___x_2296_ = lean_byte_array_size(v_array_2294_);
v___x_2297_ = lean_nat_dec_lt(v_idx_2295_, v___x_2296_);
if (v___x_2297_ == 0)
{
v_pos_2281_ = v_fst_2293_;
goto v___jp_2280_;
}
else
{
uint8_t v___x_2298_; uint32_t v___x_2299_; uint32_t v___x_2300_; uint8_t v___x_2301_; 
v___x_2298_ = lean_byte_array_fget(v_array_2294_, v_idx_2295_);
v___x_2299_ = lean_uint8_to_uint32(v___x_2298_);
v___x_2300_ = 32;
v___x_2301_ = lean_uint32_dec_eq(v___x_2299_, v___x_2300_);
if (v___x_2301_ == 0)
{
uint32_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = 9;
v___x_2303_ = lean_uint32_dec_eq(v___x_2299_, v___x_2302_);
if (v___x_2303_ == 0)
{
v_pos_2281_ = v_fst_2293_;
goto v___jp_2280_;
}
else
{
v_pos_2285_ = v_fst_2293_;
goto v___jp_2284_;
}
}
else
{
v_pos_2285_ = v_fst_2293_;
goto v___jp_2284_;
}
}
}
else
{
lean_object* v_fst_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2312_; 
v_fst_2304_ = lean_ctor_get(v_snd_2290_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_snd_2290_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v_snd_2290_, 1);
lean_dec(v_unused_2313_);
v___x_2306_ = v_snd_2290_;
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_fst_2304_);
lean_dec(v_snd_2290_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2308_ = lean_box(0);
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 1);
lean_ctor_set(v___x_2306_, 1, v___x_2308_);
v___x_2310_ = v___x_2306_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
v___jp_2280_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v_pos_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
return v___x_2283_;
}
v___jp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_pos_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
return v___x_2287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_2314_, lean_object* v_maxSpaceSequence_2315_, lean_object* v_x_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2314_, v_maxSpaceSequence_2315_, v_x_2316_, v___y_2317_);
lean_dec(v_maxSpaceSequence_2315_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_pos_2334_; lean_object* v_pos_2338_; lean_object* v___y_2342_; lean_object* v_pos_2343_; lean_object* v___y_2348_; lean_object* v_pos_2349_; lean_object* v_res_2350_; lean_object* v___y_2357_; lean_object* v_pos_2358_; lean_object* v_res_2359_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v_lower_2376_; lean_object* v_upper_2377_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v_pos_2393_; lean_object* v_pos_2397_; lean_object* v_maxSpaceSequence_2400_; lean_object* v_maxChunkExtNameLength_2401_; lean_object* v_maxChunkExtValueLength_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v_snd_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2698_; 
v_maxSpaceSequence_2400_ = lean_ctor_get(v_limits_2331_, 8);
v_maxChunkExtNameLength_2401_ = lean_ctor_get(v_limits_2331_, 11);
v_maxChunkExtValueLength_2402_ = lean_ctor_get(v_limits_2331_, 12);
v___f_2403_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2403_, v_maxSpaceSequence_2400_, v___x_2404_, v_a_2332_);
v_snd_2406_ = lean_ctor_get(v___x_2405_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2405_, 0);
lean_dec(v_unused_2699_);
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2698_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_snd_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2698_;
goto v_resetjp_2407_;
}
v___jp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_pos_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
return v___x_2336_;
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_pos_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
return v___x_2340_;
}
v___jp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___y_2342_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v_pos_2343_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
return v___x_2346_;
}
v___jp_2347_:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_2350_);
if (lean_obj_tag(v___x_2351_) == 1)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___y_2348_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v_pos_2349_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec(v___x_2351_);
lean_dec_ref(v___y_2348_);
v___x_2354_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
v___x_2355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_pos_2349_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
return v___x_2355_;
}
}
v___jp_2356_:
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2359_, v_pos_2358_);
lean_dec(v_res_2359_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_pos_2361_; lean_object* v_res_2362_; 
v_pos_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_pos_2361_);
v_res_2362_ = lean_ctor_get(v___x_2360_, 1);
lean_inc(v_res_2362_);
lean_dec_ref_known(v___x_2360_, 2);
v___y_2348_ = v___y_2357_;
v_pos_2349_ = v_pos_2361_;
v_res_2350_ = v_res_2362_;
goto v___jp_2347_;
}
else
{
lean_object* v_pos_2363_; lean_object* v_err_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v___y_2357_);
v_pos_2363_ = lean_ctor_get(v___x_2360_, 0);
v_err_2364_ = lean_ctor_get(v___x_2360_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2360_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_err_2364_);
lean_inc(v_pos_2363_);
lean_dec(v___x_2360_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_pos_2363_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_err_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
v___jp_2372_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = l_ByteArray_toByteSlice(v___y_2374_, v_lower_2376_, v_upper_2377_);
v___x_2379_ = l_ByteSlice_toByteArray(v___x_2378_);
v___x_2380_ = lean_string_validate_utf8(v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
lean_dec_ref(v___x_2379_);
v___x_2381_ = lean_box(0);
v___y_2357_ = v___y_2373_;
v_pos_2358_ = v___y_2375_;
v_res_2359_ = v___x_2381_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_string_from_utf8_unchecked(v___x_2379_);
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
v___y_2357_ = v___y_2373_;
v_pos_2358_ = v___y_2375_;
v_res_2359_ = v___x_2383_;
goto v___jp_2356_;
}
}
v___jp_2384_:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_nat_dec_le(v___y_2388_, v___y_2389_);
if (v___x_2391_ == 0)
{
lean_dec(v___y_2388_);
v___y_2373_ = v___y_2386_;
v___y_2374_ = v___y_2385_;
v___y_2375_ = v___y_2387_;
v_lower_2376_ = v___y_2390_;
v_upper_2377_ = v___y_2389_;
goto v___jp_2372_;
}
else
{
lean_dec(v___y_2389_);
v___y_2373_ = v___y_2386_;
v___y_2374_ = v___y_2385_;
v___y_2375_ = v___y_2387_;
v_lower_2376_ = v___y_2390_;
v_upper_2377_ = v___y_2388_;
goto v___jp_2372_;
}
}
v___jp_2392_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_pos_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
return v___x_2395_;
}
v___jp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_pos_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
return v___x_2399_;
}
v_resetjp_2407_:
{
lean_object* v_snd_2410_; uint8_t v___x_2411_; 
v_snd_2410_ = lean_ctor_get(v_snd_2406_, 1);
v___x_2411_ = lean_unbox(v_snd_2410_);
if (v___x_2411_ == 0)
{
lean_object* v_fst_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2686_; 
v_fst_2412_ = lean_ctor_get(v_snd_2406_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_snd_2406_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v_snd_2406_, 1);
lean_dec(v_unused_2687_);
v___x_2414_ = v_snd_2406_;
v_isShared_2415_ = v_isSharedCheck_2686_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_fst_2412_);
lean_dec(v_snd_2406_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2686_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v_array_2416_; lean_object* v_idx_2417_; lean_object* v___f_2418_; lean_object* v___y_2420_; lean_object* v_pos_2421_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v_pos_2460_; lean_object* v_array_2461_; lean_object* v_idx_2462_; lean_object* v_pos_2518_; lean_object* v_res_2519_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v_lower_2585_; lean_object* v_upper_2586_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v_pos_2601_; lean_object* v_pos_2634_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_array_2416_ = lean_ctor_get(v_fst_2412_, 0);
v_idx_2417_ = lean_ctor_get(v_fst_2412_, 1);
v___f_2418_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2678_ = lean_byte_array_size(v_array_2416_);
v___x_2679_ = lean_nat_dec_lt(v_idx_2417_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_inc(v_idx_2417_);
lean_inc_ref(v_array_2416_);
v_pos_2634_ = v_fst_2412_;
goto v___jp_2633_;
}
else
{
uint8_t v___x_2680_; uint32_t v___x_2681_; uint32_t v___x_2682_; uint8_t v___x_2683_; 
v___x_2680_ = lean_byte_array_fget(v_array_2416_, v_idx_2417_);
v___x_2681_ = lean_uint8_to_uint32(v___x_2680_);
v___x_2682_ = 32;
v___x_2683_ = lean_uint32_dec_eq(v___x_2681_, v___x_2682_);
if (v___x_2683_ == 0)
{
uint32_t v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = 9;
v___x_2685_ = lean_uint32_dec_eq(v___x_2681_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_inc(v_idx_2417_);
lean_inc_ref(v_array_2416_);
v_pos_2634_ = v_fst_2412_;
goto v___jp_2633_;
}
else
{
lean_del_object(v___x_2414_);
lean_del_object(v___x_2408_);
v_pos_2334_ = v_fst_2412_;
goto v___jp_2333_;
}
}
else
{
lean_del_object(v___x_2414_);
lean_del_object(v___x_2408_);
v_pos_2334_ = v_fst_2412_;
goto v___jp_2333_;
}
}
v___jp_2419_:
{
lean_object* v___x_2422_; 
lean_inc_ref(v_pos_2421_);
v___x_2422_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_2402_, v_pos_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_pos_2423_; lean_object* v_res_2424_; 
lean_dec_ref(v_pos_2421_);
v_pos_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_pos_2423_);
v_res_2424_ = lean_ctor_get(v___x_2422_, 1);
lean_inc(v_res_2424_);
lean_dec_ref_known(v___x_2422_, 2);
v___y_2348_ = v___y_2420_;
v_pos_2349_ = v_pos_2423_;
v_res_2350_ = v_res_2424_;
goto v___jp_2347_;
}
else
{
lean_object* v_pos_2425_; lean_object* v_err_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2456_; 
v_pos_2425_ = lean_ctor_get(v___x_2422_, 0);
v_err_2426_ = lean_ctor_get(v___x_2422_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2428_ = v___x_2422_;
v_isShared_2429_ = v_isSharedCheck_2456_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_err_2426_);
lean_inc(v_pos_2425_);
lean_dec(v___x_2422_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2456_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v_idx_2430_; lean_object* v_array_2431_; lean_object* v_idx_2432_; uint8_t v___x_2433_; 
v_idx_2430_ = lean_ctor_get(v_pos_2421_, 1);
lean_inc(v_idx_2430_);
lean_dec_ref(v_pos_2421_);
v_array_2431_ = lean_ctor_get(v_pos_2425_, 0);
v_idx_2432_ = lean_ctor_get(v_pos_2425_, 1);
v___x_2433_ = lean_nat_dec_eq(v_idx_2430_, v_idx_2432_);
lean_dec(v_idx_2430_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2435_; 
lean_dec_ref(v___y_2420_);
if (v_isShared_2429_ == 0)
{
v___x_2435_ = v___x_2428_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_pos_2425_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_err_2426_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
else
{
lean_object* v___x_2437_; lean_object* v_snd_2438_; lean_object* v_snd_2439_; uint8_t v___x_2440_; 
lean_dec(v_err_2426_);
lean_inc(v_pos_2425_);
v___x_2437_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2418_, v_maxChunkExtValueLength_2402_, v___x_2404_, v_pos_2425_);
v_snd_2438_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_snd_2438_);
v_snd_2439_ = lean_ctor_get(v_snd_2438_, 1);
v___x_2440_ = lean_unbox(v_snd_2439_);
if (v___x_2440_ == 0)
{
lean_object* v_fst_2441_; lean_object* v_fst_2442_; uint8_t v___x_2443_; 
v_fst_2441_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_fst_2441_);
lean_dec_ref(v___x_2437_);
v_fst_2442_ = lean_ctor_get(v_snd_2438_, 0);
lean_inc(v_fst_2442_);
lean_dec(v_snd_2438_);
v___x_2443_ = lean_nat_dec_eq(v_fst_2441_, v___x_2404_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
lean_inc(v_idx_2432_);
lean_inc_ref(v_array_2431_);
lean_del_object(v___x_2428_);
lean_dec(v_pos_2425_);
v___x_2444_ = lean_nat_add(v_idx_2432_, v_fst_2441_);
lean_dec(v_fst_2441_);
v___x_2445_ = lean_byte_array_size(v_array_2431_);
v___x_2446_ = lean_nat_dec_le(v_idx_2432_, v___x_2404_);
if (v___x_2446_ == 0)
{
v___y_2385_ = v_array_2431_;
v___y_2386_ = v___y_2420_;
v___y_2387_ = v_fst_2442_;
v___y_2388_ = v___x_2444_;
v___y_2389_ = v___x_2445_;
v___y_2390_ = v_idx_2432_;
goto v___jp_2384_;
}
else
{
lean_dec(v_idx_2432_);
v___y_2385_ = v_array_2431_;
v___y_2386_ = v___y_2420_;
v___y_2387_ = v_fst_2442_;
v___y_2388_ = v___x_2444_;
v___y_2389_ = v___x_2445_;
v___y_2390_ = v___x_2404_;
goto v___jp_2384_;
}
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
lean_dec(v_fst_2442_);
lean_dec(v_fst_2441_);
lean_dec_ref(v___y_2420_);
v___x_2447_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 1, v___x_2447_);
v___x_2449_ = v___x_2428_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_pos_2425_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_fst_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
lean_dec_ref(v___x_2437_);
lean_dec(v_pos_2425_);
lean_dec_ref(v___y_2420_);
v_fst_2451_ = lean_ctor_get(v_snd_2438_, 0);
lean_inc(v_fst_2451_);
lean_dec(v_snd_2438_);
v___x_2452_ = lean_box(0);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 1, v___x_2452_);
lean_ctor_set(v___x_2428_, 0, v_fst_2451_);
v___x_2454_ = v___x_2428_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_fst_2451_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
}
v___jp_2457_:
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = lean_byte_array_size(v_array_2461_);
v___x_2464_ = lean_nat_dec_lt(v_idx_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_dec(v_idx_2462_);
lean_dec_ref(v_array_2461_);
lean_dec_ref(v___y_2459_);
v___x_2465_ = lean_box(0);
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 1);
lean_ctor_set(v___x_2414_, 1, v___x_2465_);
lean_ctor_set(v___x_2414_, 0, v_pos_2460_);
v___x_2467_ = v___x_2414_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_pos_2460_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
else
{
uint8_t v___x_2469_; uint8_t v_got_2470_; uint8_t v___x_2471_; 
v___x_2469_ = 61;
v_got_2470_ = lean_byte_array_fget(v_array_2461_, v_idx_2462_);
v___x_2471_ = lean_uint8_dec_eq(v_got_2470_, v___x_2469_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_idx_2462_);
lean_dec_ref(v_array_2461_);
lean_dec_ref(v___y_2459_);
v___x_2472_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 1);
lean_ctor_set(v___x_2414_, 1, v___x_2472_);
lean_ctor_set(v___x_2414_, 0, v_pos_2460_);
v___x_2474_ = v___x_2414_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_pos_2460_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_dec_ref(v_pos_2460_);
v___x_2476_ = lean_unsigned_to_nat(1u);
v___x_2477_ = lean_nat_add(v_idx_2462_, v___x_2476_);
lean_dec(v_idx_2462_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 1, v___x_2477_);
lean_ctor_set(v___x_2414_, 0, v_array_2461_);
v___x_2479_ = v___x_2414_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_array_2461_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; 
v___x_2480_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2403_, v_maxSpaceSequence_2400_, v___y_2458_, v___x_2479_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_pos_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2505_; 
v_pos_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v___x_2480_, 1);
lean_dec(v_unused_2506_);
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2505_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_pos_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2505_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; lean_object* v_snd_2486_; lean_object* v_snd_2487_; uint8_t v___x_2488_; 
v___x_2485_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2403_, v_maxSpaceSequence_2400_, v___x_2404_, v_pos_2481_);
v_snd_2486_ = lean_ctor_get(v___x_2485_, 1);
lean_inc(v_snd_2486_);
lean_dec_ref(v___x_2485_);
v_snd_2487_ = lean_ctor_get(v_snd_2486_, 1);
v___x_2488_ = lean_unbox(v_snd_2487_);
if (v___x_2488_ == 0)
{
lean_object* v_fst_2489_; lean_object* v_array_2490_; lean_object* v_idx_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
lean_del_object(v___x_2483_);
v_fst_2489_ = lean_ctor_get(v_snd_2486_, 0);
lean_inc(v_fst_2489_);
lean_dec(v_snd_2486_);
v_array_2490_ = lean_ctor_get(v_fst_2489_, 0);
v_idx_2491_ = lean_ctor_get(v_fst_2489_, 1);
v___x_2492_ = lean_byte_array_size(v_array_2490_);
v___x_2493_ = lean_nat_dec_lt(v_idx_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
v___y_2420_ = v___y_2459_;
v_pos_2421_ = v_fst_2489_;
goto v___jp_2419_;
}
else
{
uint8_t v___x_2494_; uint32_t v___x_2495_; uint32_t v___x_2496_; uint8_t v___x_2497_; 
v___x_2494_ = lean_byte_array_fget(v_array_2490_, v_idx_2491_);
v___x_2495_ = lean_uint8_to_uint32(v___x_2494_);
v___x_2496_ = 32;
v___x_2497_ = lean_uint32_dec_eq(v___x_2495_, v___x_2496_);
if (v___x_2497_ == 0)
{
uint32_t v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = 9;
v___x_2499_ = lean_uint32_dec_eq(v___x_2495_, v___x_2498_);
if (v___x_2499_ == 0)
{
v___y_2420_ = v___y_2459_;
v_pos_2421_ = v_fst_2489_;
goto v___jp_2419_;
}
else
{
lean_dec_ref(v___y_2459_);
v_pos_2393_ = v_fst_2489_;
goto v___jp_2392_;
}
}
else
{
lean_dec_ref(v___y_2459_);
v_pos_2393_ = v_fst_2489_;
goto v___jp_2392_;
}
}
}
else
{
lean_object* v_fst_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
lean_dec_ref(v___y_2459_);
v_fst_2500_ = lean_ctor_get(v_snd_2486_, 0);
lean_inc(v_fst_2500_);
lean_dec(v_snd_2486_);
v___x_2501_ = lean_box(0);
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 1);
lean_ctor_set(v___x_2483_, 1, v___x_2501_);
lean_ctor_set(v___x_2483_, 0, v_fst_2500_);
v___x_2503_ = v___x_2483_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_fst_2500_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v_pos_2507_; lean_object* v_err_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v___y_2459_);
v_pos_2507_ = lean_ctor_get(v___x_2480_, 0);
v_err_2508_ = lean_ctor_get(v___x_2480_, 1);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2480_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_err_2508_);
lean_inc(v_pos_2507_);
lean_dec(v___x_2480_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_pos_2507_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_err_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
}
}
v___jp_2517_:
{
lean_object* v___x_2520_; 
v___x_2520_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2519_, v_pos_2518_);
lean_dec(v_res_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_pos_2521_; lean_object* v_res_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_pos_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_pos_2521_);
v_res_2522_ = lean_ctor_get(v___x_2520_, 1);
lean_inc(v_res_2522_);
lean_dec_ref_known(v___x_2520_, 2);
v___x_2523_ = lean_box(0);
v___x_2524_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2403_, v_maxSpaceSequence_2400_, v___x_2523_, v_pos_2521_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_pos_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2562_; 
v_pos_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2524_, 1);
lean_dec(v_unused_2563_);
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2562_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_pos_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2562_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_2522_);
if (lean_obj_tag(v___x_2529_) == 1)
{
lean_object* v_val_2530_; lean_object* v_array_2531_; lean_object* v_idx_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_val_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_val_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v_array_2531_ = lean_ctor_get(v_pos_2525_, 0);
v_idx_2532_ = lean_ctor_get(v_pos_2525_, 1);
v___x_2533_ = lean_byte_array_size(v_array_2531_);
v___x_2534_ = lean_nat_dec_lt(v_idx_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_del_object(v___x_2527_);
lean_del_object(v___x_2414_);
v___y_2342_ = v_val_2530_;
v_pos_2343_ = v_pos_2525_;
goto v___jp_2341_;
}
else
{
uint8_t v___x_2535_; uint8_t v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_byte_array_fget(v_array_2531_, v_idx_2532_);
v___x_2536_ = 61;
v___x_2537_ = lean_uint8_dec_eq(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_del_object(v___x_2527_);
lean_del_object(v___x_2414_);
v___y_2342_ = v_val_2530_;
v_pos_2343_ = v_pos_2525_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2538_; lean_object* v_snd_2539_; lean_object* v_snd_2540_; uint8_t v___x_2541_; 
v___x_2538_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2403_, v_maxSpaceSequence_2400_, v___x_2404_, v_pos_2525_);
v_snd_2539_ = lean_ctor_get(v___x_2538_, 1);
lean_inc(v_snd_2539_);
lean_dec_ref(v___x_2538_);
v_snd_2540_ = lean_ctor_get(v_snd_2539_, 1);
v___x_2541_ = lean_unbox(v_snd_2540_);
if (v___x_2541_ == 0)
{
lean_object* v_fst_2542_; lean_object* v_array_2543_; lean_object* v_idx_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
lean_del_object(v___x_2527_);
v_fst_2542_ = lean_ctor_get(v_snd_2539_, 0);
lean_inc(v_fst_2542_);
lean_dec(v_snd_2539_);
v_array_2543_ = lean_ctor_get(v_fst_2542_, 0);
v_idx_2544_ = lean_ctor_get(v_fst_2542_, 1);
v___x_2545_ = lean_byte_array_size(v_array_2543_);
v___x_2546_ = lean_nat_dec_lt(v_idx_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_inc(v_idx_2544_);
lean_inc_ref(v_array_2543_);
v___y_2458_ = v___x_2523_;
v___y_2459_ = v_val_2530_;
v_pos_2460_ = v_fst_2542_;
v_array_2461_ = v_array_2543_;
v_idx_2462_ = v_idx_2544_;
goto v___jp_2457_;
}
else
{
uint8_t v___x_2547_; uint32_t v___x_2548_; uint32_t v___x_2549_; uint8_t v___x_2550_; 
v___x_2547_ = lean_byte_array_fget(v_array_2543_, v_idx_2544_);
v___x_2548_ = lean_uint8_to_uint32(v___x_2547_);
v___x_2549_ = 32;
v___x_2550_ = lean_uint32_dec_eq(v___x_2548_, v___x_2549_);
if (v___x_2550_ == 0)
{
uint32_t v___x_2551_; uint8_t v___x_2552_; 
v___x_2551_ = 9;
v___x_2552_ = lean_uint32_dec_eq(v___x_2548_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_inc(v_idx_2544_);
lean_inc_ref(v_array_2543_);
v___y_2458_ = v___x_2523_;
v___y_2459_ = v_val_2530_;
v_pos_2460_ = v_fst_2542_;
v_array_2461_ = v_array_2543_;
v_idx_2462_ = v_idx_2544_;
goto v___jp_2457_;
}
else
{
lean_dec(v_val_2530_);
lean_del_object(v___x_2414_);
v_pos_2397_ = v_fst_2542_;
goto v___jp_2396_;
}
}
else
{
lean_dec(v_val_2530_);
lean_del_object(v___x_2414_);
v_pos_2397_ = v_fst_2542_;
goto v___jp_2396_;
}
}
}
else
{
lean_object* v_fst_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_dec(v_val_2530_);
lean_del_object(v___x_2414_);
v_fst_2553_ = lean_ctor_get(v_snd_2539_, 0);
lean_inc(v_fst_2553_);
lean_dec(v_snd_2539_);
v___x_2554_ = lean_box(0);
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 1);
lean_ctor_set(v___x_2527_, 1, v___x_2554_);
lean_ctor_set(v___x_2527_, 0, v_fst_2553_);
v___x_2556_ = v___x_2527_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_fst_2553_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_dec(v___x_2529_);
lean_del_object(v___x_2414_);
v___x_2558_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 1);
lean_ctor_set(v___x_2527_, 1, v___x_2558_);
v___x_2560_ = v___x_2527_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_pos_2525_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_pos_2564_; lean_object* v_err_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_res_2522_);
lean_del_object(v___x_2414_);
v_pos_2564_ = lean_ctor_get(v___x_2524_, 0);
v_err_2565_ = lean_ctor_get(v___x_2524_, 1);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2524_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_err_2565_);
lean_inc(v_pos_2564_);
lean_dec(v___x_2524_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_pos_2564_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_err_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v_pos_2573_; lean_object* v_err_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_del_object(v___x_2414_);
v_pos_2573_ = lean_ctor_get(v___x_2520_, 0);
v_err_2574_ = lean_ctor_get(v___x_2520_, 1);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2520_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_err_2574_);
lean_inc(v_pos_2573_);
lean_dec(v___x_2520_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_pos_2573_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_err_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
v___jp_2582_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = l_ByteArray_toByteSlice(v___y_2584_, v_lower_2585_, v_upper_2586_);
v___x_2588_ = l_ByteSlice_toByteArray(v___x_2587_);
v___x_2589_ = lean_string_validate_utf8(v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref(v___x_2588_);
v___x_2590_ = lean_box(0);
v_pos_2518_ = v___y_2583_;
v_res_2519_ = v___x_2590_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_string_from_utf8_unchecked(v___x_2588_);
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
v_pos_2518_ = v___y_2583_;
v_res_2519_ = v___x_2592_;
goto v___jp_2517_;
}
}
v___jp_2593_:
{
uint8_t v___x_2599_; 
v___x_2599_ = lean_nat_dec_le(v___y_2594_, v___y_2596_);
if (v___x_2599_ == 0)
{
lean_dec(v___y_2594_);
v___y_2583_ = v___y_2595_;
v___y_2584_ = v___y_2597_;
v_lower_2585_ = v___y_2598_;
v_upper_2586_ = v___y_2596_;
goto v___jp_2582_;
}
else
{
lean_dec(v___y_2596_);
v___y_2583_ = v___y_2595_;
v___y_2584_ = v___y_2597_;
v_lower_2585_ = v___y_2598_;
v_upper_2586_ = v___y_2594_;
goto v___jp_2582_;
}
}
v___jp_2600_:
{
lean_object* v___x_2602_; lean_object* v_snd_2603_; lean_object* v_snd_2604_; uint8_t v___x_2605_; 
lean_inc_ref(v_pos_2601_);
v___x_2602_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2418_, v_maxChunkExtNameLength_2401_, v___x_2404_, v_pos_2601_);
v_snd_2603_ = lean_ctor_get(v___x_2602_, 1);
lean_inc(v_snd_2603_);
v_snd_2604_ = lean_ctor_get(v_snd_2603_, 1);
v___x_2605_ = lean_unbox(v_snd_2604_);
if (v___x_2605_ == 0)
{
lean_object* v_fst_2606_; lean_object* v_fst_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2621_; 
v_fst_2606_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_fst_2606_);
lean_dec_ref(v___x_2602_);
v_fst_2607_ = lean_ctor_get(v_snd_2603_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v_snd_2603_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v_snd_2603_, 1);
lean_dec(v_unused_2622_);
v___x_2609_ = v_snd_2603_;
v_isShared_2610_ = v_isSharedCheck_2621_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_fst_2607_);
lean_dec(v_snd_2603_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2621_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
uint8_t v___x_2611_; 
v___x_2611_ = lean_nat_dec_eq(v_fst_2606_, v___x_2404_);
if (v___x_2611_ == 0)
{
lean_object* v_array_2612_; lean_object* v_idx_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
lean_del_object(v___x_2609_);
v_array_2612_ = lean_ctor_get(v_pos_2601_, 0);
lean_inc_ref(v_array_2612_);
v_idx_2613_ = lean_ctor_get(v_pos_2601_, 1);
lean_inc(v_idx_2613_);
lean_dec_ref(v_pos_2601_);
v___x_2614_ = lean_nat_add(v_idx_2613_, v_fst_2606_);
lean_dec(v_fst_2606_);
v___x_2615_ = lean_byte_array_size(v_array_2612_);
v___x_2616_ = lean_nat_dec_le(v_idx_2613_, v___x_2404_);
if (v___x_2616_ == 0)
{
v___y_2594_ = v___x_2614_;
v___y_2595_ = v_fst_2607_;
v___y_2596_ = v___x_2615_;
v___y_2597_ = v_array_2612_;
v___y_2598_ = v_idx_2613_;
goto v___jp_2593_;
}
else
{
lean_dec(v_idx_2613_);
v___y_2594_ = v___x_2614_;
v___y_2595_ = v_fst_2607_;
v___y_2596_ = v___x_2615_;
v___y_2597_ = v_array_2612_;
v___y_2598_ = v___x_2404_;
goto v___jp_2593_;
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_dec(v_fst_2607_);
lean_dec(v_fst_2606_);
lean_del_object(v___x_2414_);
v___x_2617_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 1);
lean_ctor_set(v___x_2609_, 1, v___x_2617_);
lean_ctor_set(v___x_2609_, 0, v_pos_2601_);
v___x_2619_ = v___x_2609_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_pos_2601_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_fst_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v___x_2602_);
lean_dec_ref(v_pos_2601_);
lean_del_object(v___x_2414_);
v_fst_2623_ = lean_ctor_get(v_snd_2603_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_snd_2603_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v_snd_2603_, 1);
lean_dec(v_unused_2632_);
v___x_2625_ = v_snd_2603_;
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_fst_2623_);
lean_dec(v_snd_2603_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2627_ = lean_box(0);
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 1);
lean_ctor_set(v___x_2625_, 1, v___x_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_fst_2623_);
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
v___jp_2633_:
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = lean_byte_array_size(v_array_2416_);
v___x_2636_ = lean_nat_dec_lt(v_idx_2417_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_dec(v_idx_2417_);
lean_dec_ref(v_array_2416_);
lean_del_object(v___x_2414_);
v___x_2637_ = lean_box(0);
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 1);
lean_ctor_set(v___x_2408_, 1, v___x_2637_);
lean_ctor_set(v___x_2408_, 0, v_pos_2634_);
v___x_2639_ = v___x_2408_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_pos_2634_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
else
{
uint8_t v___x_2641_; uint8_t v_got_2642_; uint8_t v___x_2643_; 
v___x_2641_ = 59;
v_got_2642_ = lean_byte_array_fget(v_array_2416_, v_idx_2417_);
v___x_2643_ = lean_uint8_dec_eq(v_got_2642_, v___x_2641_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
lean_dec(v_idx_2417_);
lean_dec_ref(v_array_2416_);
lean_del_object(v___x_2414_);
v___x_2644_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7));
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 1);
lean_ctor_set(v___x_2408_, 1, v___x_2644_);
lean_ctor_set(v___x_2408_, 0, v_pos_2634_);
v___x_2646_ = v___x_2408_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_pos_2634_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
lean_dec_ref(v_pos_2634_);
v___x_2648_ = lean_unsigned_to_nat(1u);
v___x_2649_ = lean_nat_add(v_idx_2417_, v___x_2648_);
lean_dec(v_idx_2417_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v___x_2649_);
lean_ctor_set(v___x_2408_, 0, v_array_2416_);
v___x_2651_ = v___x_2408_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_array_2416_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v_snd_2653_; lean_object* v_snd_2654_; uint8_t v___x_2655_; 
v___x_2652_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2403_, v_maxSpaceSequence_2400_, v___x_2404_, v___x_2651_);
v_snd_2653_ = lean_ctor_get(v___x_2652_, 1);
lean_inc(v_snd_2653_);
lean_dec_ref(v___x_2652_);
v_snd_2654_ = lean_ctor_get(v_snd_2653_, 1);
v___x_2655_ = lean_unbox(v_snd_2654_);
if (v___x_2655_ == 0)
{
lean_object* v_fst_2656_; lean_object* v_array_2657_; lean_object* v_idx_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v_fst_2656_ = lean_ctor_get(v_snd_2653_, 0);
lean_inc(v_fst_2656_);
lean_dec(v_snd_2653_);
v_array_2657_ = lean_ctor_get(v_fst_2656_, 0);
v_idx_2658_ = lean_ctor_get(v_fst_2656_, 1);
v___x_2659_ = lean_byte_array_size(v_array_2657_);
v___x_2660_ = lean_nat_dec_lt(v_idx_2658_, v___x_2659_);
if (v___x_2660_ == 0)
{
v_pos_2601_ = v_fst_2656_;
goto v___jp_2600_;
}
else
{
uint8_t v___x_2661_; uint32_t v___x_2662_; uint32_t v___x_2663_; uint8_t v___x_2664_; 
v___x_2661_ = lean_byte_array_fget(v_array_2657_, v_idx_2658_);
v___x_2662_ = lean_uint8_to_uint32(v___x_2661_);
v___x_2663_ = 32;
v___x_2664_ = lean_uint32_dec_eq(v___x_2662_, v___x_2663_);
if (v___x_2664_ == 0)
{
uint32_t v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = 9;
v___x_2666_ = lean_uint32_dec_eq(v___x_2662_, v___x_2665_);
if (v___x_2666_ == 0)
{
v_pos_2601_ = v_fst_2656_;
goto v___jp_2600_;
}
else
{
lean_del_object(v___x_2414_);
v_pos_2338_ = v_fst_2656_;
goto v___jp_2337_;
}
}
else
{
lean_del_object(v___x_2414_);
v_pos_2338_ = v_fst_2656_;
goto v___jp_2337_;
}
}
}
else
{
lean_object* v_fst_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2675_; 
lean_del_object(v___x_2414_);
v_fst_2667_ = lean_ctor_get(v_snd_2653_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_snd_2653_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v_snd_2653_, 1);
lean_dec(v_unused_2676_);
v___x_2669_ = v_snd_2653_;
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_fst_2667_);
lean_dec(v_snd_2653_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2671_ = lean_box(0);
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
lean_ctor_set(v___x_2669_, 1, v___x_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_fst_2667_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
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
lean_object* v_fst_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2696_; 
lean_del_object(v___x_2408_);
v_fst_2688_ = lean_ctor_get(v_snd_2406_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_snd_2406_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v_snd_2406_, 1);
lean_dec(v_unused_2697_);
v___x_2690_ = v_snd_2406_;
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_fst_2688_);
lean_dec(v_snd_2406_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = lean_box(0);
if (v_isShared_2691_ == 0)
{
lean_ctor_set_tag(v___x_2690_, 1);
lean_ctor_set(v___x_2690_, 1, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_fst_2688_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2700_, v_a_2701_);
lean_dec_ref(v_limits_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2705_; 
lean_inc_ref(v___y_2704_);
v___x_2705_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_pos_2706_; lean_object* v_res_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v___y_2704_);
v_pos_2706_ = lean_ctor_get(v___x_2705_, 0);
v_res_2707_ = lean_ctor_get(v___x_2705_, 1);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2709_ = v___x_2705_;
v_isShared_2710_ = v_isSharedCheck_2715_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_res_2707_);
lean_inc(v_pos_2706_);
lean_dec(v___x_2705_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2715_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_res_2707_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 1, v___x_2711_);
v___x_2713_ = v___x_2709_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_pos_2706_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
else
{
lean_object* v_err_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2729_; 
v_err_2716_ = lean_ctor_get(v___x_2705_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v___x_2705_, 0);
lean_dec(v_unused_2730_);
v___x_2718_ = v___x_2705_;
v_isShared_2719_ = v_isSharedCheck_2729_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_err_2716_);
lean_dec(v___x_2705_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2729_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v_idx_2720_; uint8_t v___x_2721_; 
v_idx_2720_ = lean_ctor_get(v___y_2704_, 1);
v___x_2721_ = lean_nat_dec_eq(v_idx_2720_, v_idx_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2723_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___y_2704_);
v___x_2723_ = v___x_2718_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___y_2704_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_err_2716_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_dec(v_err_2716_);
v___x_2725_ = lean_box(0);
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 0);
lean_ctor_set(v___x_2718_, 1, v___x_2725_);
lean_ctor_set(v___x_2718_, 0, v___y_2704_);
v___x_2727_ = v___x_2718_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___y_2704_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_2731_, v___y_2732_);
lean_dec_ref(v_limits_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_pos_2737_; lean_object* v_res_2738_; lean_object* v_maxChunkExtensions_2739_; lean_object* v___f_2740_; lean_object* v___x_2741_; 
v_pos_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_pos_2737_);
v_res_2738_ = lean_ctor_get(v___x_2736_, 1);
lean_inc(v_res_2738_);
lean_dec_ref_known(v___x_2736_, 2);
v_maxChunkExtensions_2739_ = lean_ctor_get(v_limits_2734_, 10);
lean_inc(v_maxChunkExtensions_2739_);
v___f_2740_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2740_, 0, v_limits_2734_);
v___x_2741_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_2740_, v_maxChunkExtensions_2739_, v_pos_2737_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_pos_2742_; lean_object* v_res_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_pos_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_pos_2742_);
v_res_2743_ = lean_ctor_get(v___x_2741_, 1);
lean_inc(v_res_2743_);
lean_dec_ref_known(v___x_2741_, 2);
v___x_2744_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2745_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2744_, v_pos_2742_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_pos_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2754_; 
v_pos_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v___x_2745_, 1);
lean_dec(v_unused_2755_);
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_pos_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_res_2738_);
lean_ctor_set(v___x_2750_, 1, v_res_2743_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 1, v___x_2750_);
v___x_2752_ = v___x_2748_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_pos_2746_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_pos_2756_; lean_object* v_err_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_res_2743_);
lean_dec(v_res_2738_);
v_pos_2756_ = lean_ctor_get(v___x_2745_, 0);
v_err_2757_ = lean_ctor_get(v___x_2745_, 1);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2745_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_err_2757_);
lean_inc(v_pos_2756_);
lean_dec(v___x_2745_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_pos_2756_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_err_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_pos_2765_; lean_object* v_err_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_res_2738_);
v_pos_2765_ = lean_ctor_get(v___x_2741_, 0);
v_err_2766_ = lean_ctor_get(v___x_2741_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2741_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_err_2766_);
lean_inc(v_pos_2765_);
lean_dec(v___x_2741_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_pos_2765_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_err_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_pos_2774_; lean_object* v_err_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec_ref(v_limits_2734_);
v_pos_2774_ = lean_ctor_get(v___x_2736_, 0);
v_err_2775_ = lean_ctor_get(v___x_2736_, 1);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2736_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_err_2775_);
lean_inc(v_pos_2774_);
lean_dec(v___x_2736_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_pos_2774_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_err_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object* v_x_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_obj_tag_nat(v_x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object* v_x_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(v_x_2785_);
lean_dec_ref(v_x_2785_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_2787_, lean_object* v_k_2788_){
_start:
{
if (lean_obj_tag(v_t_2787_) == 0)
{
lean_object* v_data_2789_; lean_object* v___x_2790_; 
v_data_2789_ = lean_ctor_get(v_t_2787_, 0);
lean_inc_ref(v_data_2789_);
lean_dec_ref_known(v_t_2787_, 1);
v___x_2790_ = lean_apply_1(v_k_2788_, v_data_2789_);
return v___x_2790_;
}
else
{
lean_object* v_data_2791_; lean_object* v_remaining_2792_; lean_object* v___x_2793_; 
v_data_2791_ = lean_ctor_get(v_t_2787_, 0);
lean_inc_ref(v_data_2791_);
v_remaining_2792_ = lean_ctor_get(v_t_2787_, 1);
lean_inc(v_remaining_2792_);
lean_dec_ref_known(v_t_2787_, 2);
v___x_2793_ = lean_apply_2(v_k_2788_, v_data_2791_, v_remaining_2792_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_2794_, lean_object* v_ctorIdx_2795_, lean_object* v_t_2796_, lean_object* v_h_2797_, lean_object* v_k_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2796_, v_k_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_2800_, lean_object* v_ctorIdx_2801_, lean_object* v_t_2802_, lean_object* v_h_2803_, lean_object* v_k_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_2800_, v_ctorIdx_2801_, v_t_2802_, v_h_2803_, v_k_2804_);
lean_dec(v_ctorIdx_2801_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_2806_, lean_object* v_complete_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2806_, v_complete_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_2809_, lean_object* v_t_2810_, lean_object* v_h_2811_, lean_object* v_complete_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2810_, v_complete_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_2814_, lean_object* v_incomplete_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2814_, v_incomplete_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_2817_, lean_object* v_t_2818_, lean_object* v_h_2819_, lean_object* v_incomplete_2820_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2818_, v_incomplete_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_2822_, v_a_2823_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_res_2825_; lean_object* v_pos_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2866_; 
v_res_2825_ = lean_ctor_get(v___x_2824_, 1);
v_pos_2826_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2828_ = v___x_2824_;
v_isShared_2829_ = v_isSharedCheck_2866_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_res_2825_);
lean_inc(v_pos_2826_);
lean_dec(v___x_2824_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2866_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_fst_2830_; lean_object* v_snd_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2865_; 
v_fst_2830_ = lean_ctor_get(v_res_2825_, 0);
v_snd_2831_ = lean_ctor_get(v_res_2825_, 1);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_res_2825_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2833_ = v_res_2825_;
v_isShared_2834_ = v_isSharedCheck_2865_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_snd_2831_);
lean_inc(v_fst_2830_);
lean_dec(v_res_2825_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2865_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = lean_unsigned_to_nat(0u);
v___x_2836_ = lean_nat_dec_eq(v_fst_2830_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; 
lean_del_object(v___x_2828_);
v___x_2837_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_2830_, v_pos_2826_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_pos_2838_; lean_object* v_res_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2851_; 
v_pos_2838_ = lean_ctor_get(v___x_2837_, 0);
v_res_2839_ = lean_ctor_get(v___x_2837_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2841_ = v___x_2837_;
v_isShared_2842_ = v_isSharedCheck_2851_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_res_2839_);
lean_inc(v_pos_2838_);
lean_dec(v___x_2837_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2851_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 1, v_res_2839_);
lean_ctor_set(v___x_2833_, 0, v_snd_2831_);
v___x_2844_ = v___x_2833_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_snd_2831_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_res_2839_);
v___x_2844_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_fst_2830_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 1, v___x_2846_);
v___x_2848_ = v___x_2841_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_pos_2838_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_pos_2852_; lean_object* v_err_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_del_object(v___x_2833_);
lean_dec(v_snd_2831_);
lean_dec(v_fst_2830_);
v_pos_2852_ = lean_ctor_get(v___x_2837_, 0);
v_err_2853_ = lean_ctor_get(v___x_2837_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2837_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_err_2853_);
lean_inc(v_pos_2852_);
lean_dec(v___x_2837_);
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
else
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
lean_del_object(v___x_2833_);
lean_dec(v_snd_2831_);
lean_dec(v_fst_2830_);
v___x_2861_ = lean_box(0);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 1, v___x_2861_);
v___x_2863_ = v___x_2828_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_pos_2826_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
else
{
lean_object* v_pos_2867_; lean_object* v_err_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
v_pos_2867_ = lean_ctor_get(v___x_2824_, 0);
v_err_2868_ = lean_ctor_get(v___x_2824_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2824_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_err_2868_);
lean_inc(v_pos_2867_);
lean_dec(v___x_2824_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_pos_2867_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_err_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_2876_, lean_object* v_it_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2878_ = l_ByteArray_Iterator_remainingBytes(v_it_2877_);
v___x_2879_ = lean_unsigned_to_nat(0u);
v___x_2880_ = lean_nat_dec_eq(v___x_2878_, v___x_2879_);
if (v___x_2880_ == 0)
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_nat_dec_lt(v___x_2878_, v_size_2876_);
if (v___x_2881_ == 0)
{
lean_object* v_array_2882_; lean_object* v_idx_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v___x_2878_);
v_array_2882_ = lean_ctor_get(v_it_2877_, 0);
v_idx_2883_ = lean_ctor_get(v_it_2877_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_it_2877_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2885_ = v_it_2877_;
v_isShared_2886_ = v_isSharedCheck_2902_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_idx_2883_);
lean_inc(v_array_2882_);
lean_dec(v_it_2877_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2902_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2887_ = lean_nat_add(v_idx_2883_, v_size_2876_);
lean_inc(v___x_2887_);
lean_inc_ref(v_array_2882_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v___x_2887_);
v___x_2889_ = v___x_2885_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_array_2882_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v_lower_2891_; lean_object* v_upper_2892_; lean_object* v___x_2896_; lean_object* v___y_2898_; uint8_t v___x_2900_; 
v___x_2896_ = lean_byte_array_size(v_array_2882_);
v___x_2900_ = lean_nat_dec_le(v_idx_2883_, v___x_2879_);
if (v___x_2900_ == 0)
{
v___y_2898_ = v_idx_2883_;
goto v___jp_2897_;
}
else
{
lean_dec(v_idx_2883_);
v___y_2898_ = v___x_2879_;
goto v___jp_2897_;
}
v___jp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2893_ = l_ByteArray_toByteSlice(v_array_2882_, v_lower_2891_, v_upper_2892_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2889_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
return v___x_2895_;
}
v___jp_2897_:
{
uint8_t v___x_2899_; 
v___x_2899_ = lean_nat_dec_le(v___x_2887_, v___x_2896_);
if (v___x_2899_ == 0)
{
lean_dec(v___x_2887_);
v_lower_2891_ = v___y_2898_;
v_upper_2892_ = v___x_2896_;
goto v___jp_2890_;
}
else
{
v_lower_2891_ = v___y_2898_;
v_upper_2892_ = v___x_2887_;
goto v___jp_2890_;
}
}
}
}
}
else
{
lean_object* v_array_2903_; lean_object* v_idx_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2924_; 
v_array_2903_ = lean_ctor_get(v_it_2877_, 0);
v_idx_2904_ = lean_ctor_get(v_it_2877_, 1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_it_2877_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2906_ = v_it_2877_;
v_isShared_2907_ = v_isSharedCheck_2924_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_idx_2904_);
lean_inc(v_array_2903_);
lean_dec(v_it_2877_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2924_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2908_ = lean_nat_add(v_idx_2904_, v___x_2878_);
lean_inc(v___x_2908_);
lean_inc_ref(v_array_2903_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 1, v___x_2908_);
v___x_2910_ = v___x_2906_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_array_2903_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v_lower_2912_; lean_object* v_upper_2913_; lean_object* v___x_2918_; lean_object* v___y_2920_; uint8_t v___x_2922_; 
v___x_2918_ = lean_byte_array_size(v_array_2903_);
v___x_2922_ = lean_nat_dec_le(v_idx_2904_, v___x_2879_);
if (v___x_2922_ == 0)
{
v___y_2920_ = v_idx_2904_;
goto v___jp_2919_;
}
else
{
lean_dec(v_idx_2904_);
v___y_2920_ = v___x_2879_;
goto v___jp_2919_;
}
v___jp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2914_ = l_ByteArray_toByteSlice(v_array_2903_, v_lower_2912_, v_upper_2913_);
v___x_2915_ = lean_nat_sub(v_size_2876_, v___x_2878_);
lean_dec(v___x_2878_);
v___x_2916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2910_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
return v___x_2917_;
}
v___jp_2919_:
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_nat_dec_le(v___x_2908_, v___x_2918_);
if (v___x_2921_ == 0)
{
lean_dec(v___x_2908_);
v_lower_2912_ = v___y_2920_;
v_upper_2913_ = v___x_2918_;
goto v___jp_2911_;
}
else
{
v_lower_2912_ = v___y_2920_;
v_upper_2913_ = v___x_2908_;
goto v___jp_2911_;
}
}
}
}
}
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec(v___x_2878_);
v___x_2925_ = lean_box(0);
v___x_2926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2926_, 0, v_it_2877_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
return v___x_2926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_2927_, lean_object* v_it_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_2927_, v_it_2928_);
lean_dec(v_size_2927_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_res_2933_; 
v_res_2933_ = lean_ctor_get(v___x_2932_, 1);
if (lean_obj_tag(v_res_2933_) == 0)
{
lean_object* v_pos_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_inc_ref(v_res_2933_);
v_pos_2934_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_pos_2934_);
lean_dec_ref_known(v___x_2932_, 2);
v___x_2935_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2936_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2935_, v_pos_2934_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_pos_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
v_pos_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v___x_2936_, 1);
lean_dec(v_unused_2945_);
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_pos_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v_res_2933_);
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_pos_2937_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_res_2933_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_pos_2946_; lean_object* v_err_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec_ref_known(v_res_2933_, 1);
v_pos_2946_ = lean_ctor_get(v___x_2936_, 0);
v_err_2947_ = lean_ctor_get(v___x_2936_, 1);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2936_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_err_2947_);
lean_inc(v_pos_2946_);
lean_dec(v___x_2936_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_pos_2946_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_err_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
return v___x_2932_;
}
}
else
{
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_2955_, v_a_2956_);
lean_dec(v_size_2955_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object* v_s_2958_, lean_object* v_p_2959_){
_start:
{
lean_object* v___y_2961_; lean_object* v___y_2962_; uint32_t v___y_2966_; lean_object* v___x_2978_; uint8_t v_decide_2979_; 
v___x_2978_ = lean_string_utf8_byte_size(v_s_2958_);
v_decide_2979_ = lean_nat_dec_eq(v_p_2959_, v___x_2978_);
if (v_decide_2979_ == 0)
{
uint32_t v___x_2980_; uint32_t v___x_2981_; uint8_t v___x_2982_; 
v___x_2980_ = lean_string_utf8_get_fast(v_s_2958_, v_p_2959_);
v___x_2981_ = 65;
v___x_2982_ = lean_uint32_dec_le(v___x_2981_, v___x_2980_);
if (v___x_2982_ == 0)
{
v___y_2966_ = v___x_2980_;
goto v___jp_2965_;
}
else
{
uint32_t v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = 90;
v___x_2984_ = lean_uint32_dec_le(v___x_2980_, v___x_2983_);
if (v___x_2984_ == 0)
{
v___y_2966_ = v___x_2980_;
goto v___jp_2965_;
}
else
{
uint32_t v___x_2985_; uint32_t v___x_2986_; 
v___x_2985_ = 32;
v___x_2986_ = lean_uint32_add(v___x_2980_, v___x_2985_);
v___y_2966_ = v___x_2986_;
goto v___jp_2965_;
}
}
}
else
{
lean_dec(v_p_2959_);
return v_s_2958_;
}
v___jp_2960_:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_nat_add(v_p_2959_, v___y_2962_);
lean_dec(v_p_2959_);
v_s_2958_ = v___y_2961_;
v_p_2959_ = v___x_2963_;
goto _start;
}
v___jp_2965_:
{
lean_object* v___x_2967_; uint32_t v___x_2968_; uint8_t v___x_2969_; 
lean_inc(v_p_2959_);
v___x_2967_ = lean_string_utf8_set(v_s_2958_, v_p_2959_, v___y_2966_);
v___x_2968_ = 127;
v___x_2969_ = lean_uint32_dec_le(v___y_2966_, v___x_2968_);
if (v___x_2969_ == 0)
{
uint32_t v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = 2047;
v___x_2971_ = lean_uint32_dec_le(v___y_2966_, v___x_2970_);
if (v___x_2971_ == 0)
{
uint32_t v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = 65535;
v___x_2973_ = lean_uint32_dec_le(v___y_2966_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_unsigned_to_nat(4u);
v___y_2961_ = v___x_2967_;
v___y_2962_ = v___x_2974_;
goto v___jp_2960_;
}
else
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_unsigned_to_nat(3u);
v___y_2961_ = v___x_2967_;
v___y_2962_ = v___x_2975_;
goto v___jp_2960_;
}
}
else
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_unsigned_to_nat(2u);
v___y_2961_ = v___x_2967_;
v___y_2962_ = v___x_2976_;
goto v___jp_2960_;
}
}
else
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_unsigned_to_nat(1u);
v___y_2961_ = v___x_2967_;
v___y_2962_ = v___x_2977_;
goto v___jp_2960_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_2999_){
_start:
{
lean_object* v___x_3000_; lean_object* v_n_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3000_ = lean_unsigned_to_nat(0u);
v_n_3001_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(v_name_2999_, v___x_3000_);
v___x_3002_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3003_ = lean_string_dec_eq(v_n_3001_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3005_ = lean_string_dec_eq(v_n_3001_, v___x_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3007_ = lean_string_dec_eq(v_n_3001_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3008_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3009_ = lean_string_dec_eq(v_n_3001_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3011_ = lean_string_dec_eq(v_n_3001_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5));
v___x_3013_ = lean_string_dec_eq(v_n_3001_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3014_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6));
v___x_3015_ = lean_string_dec_eq(v_n_3001_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7));
v___x_3017_ = lean_string_dec_eq(v_n_3001_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8));
v___x_3019_ = lean_string_dec_eq(v_n_3001_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9));
v___x_3021_ = lean_string_dec_eq(v_n_3001_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10));
v___x_3023_ = lean_string_dec_eq(v_n_3001_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11));
v___x_3025_ = lean_string_dec_eq(v_n_3001_, v___x_3024_);
lean_dec_ref(v_n_3001_);
return v___x_3025_;
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3023_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3021_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3019_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3017_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3015_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3013_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3011_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3009_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3007_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3005_;
}
}
else
{
lean_dec_ref(v_n_3001_);
return v___x_3003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3026_){
_start:
{
uint8_t v_res_3027_; lean_object* v_r_3028_; 
v_res_3027_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3026_);
v_r_3028_ = lean_box(v_res_3027_);
return v_r_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_res_3033_; 
v_res_3033_ = lean_ctor_get(v___x_3032_, 1);
lean_inc(v_res_3033_);
if (lean_obj_tag(v_res_3033_) == 1)
{
lean_object* v_val_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3055_; 
v_val_3034_ = lean_ctor_get(v_res_3033_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_res_3033_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3036_ = v_res_3033_;
v_isShared_3037_ = v_isSharedCheck_3055_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_val_3034_);
lean_dec(v_res_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3055_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v_pos_3038_; lean_object* v_fst_3039_; uint8_t v___x_3040_; 
v_pos_3038_ = lean_ctor_get(v___x_3032_, 0);
v_fst_3039_ = lean_ctor_get(v_val_3034_, 0);
lean_inc_n(v_fst_3039_, 2);
lean_dec(v_val_3034_);
v___x_3040_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3039_);
if (v___x_3040_ == 0)
{
lean_dec(v_fst_3039_);
lean_del_object(v___x_3036_);
return v___x_3032_;
}
else
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3052_; 
lean_inc(v_pos_3038_);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; lean_object* v_unused_3054_; 
v_unused_3053_ = lean_ctor_get(v___x_3032_, 1);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v___x_3032_, 0);
lean_dec(v_unused_3054_);
v___x_3042_ = v___x_3032_;
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v___x_3032_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3044_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3045_ = lean_string_append(v___x_3044_, v_fst_3039_);
lean_dec(v_fst_3039_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3045_);
v___x_3047_ = v___x_3036_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3049_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set_tag(v___x_3042_, 1);
lean_ctor_set(v___x_3042_, 1, v___x_3047_);
v___x_3049_ = v___x_3042_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_pos_3038_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3033_);
return v___x_3032_;
}
}
else
{
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3056_, v_a_3057_);
lean_dec_ref(v_limits_3056_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_maxTrailerHeaders_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_maxTrailerHeaders_3061_ = lean_ctor_get(v_limits_3059_, 17);
lean_inc(v_maxTrailerHeaders_3061_);
v___x_3062_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3062_, 0, v_limits_3059_);
v___x_3063_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3062_, v_maxTrailerHeaders_3061_, v_a_3060_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_pos_3064_; lean_object* v_res_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_pos_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_pos_3064_);
v_res_3065_ = lean_ctor_get(v___x_3063_, 1);
lean_inc(v_res_3065_);
lean_dec_ref_known(v___x_3063_, 2);
v___x_3066_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3067_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3066_, v_pos_3064_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_pos_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
v_pos_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v___x_3067_, 1);
lean_dec(v_unused_3076_);
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_pos_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 1, v_res_3065_);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_pos_3068_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_res_3065_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
lean_object* v_pos_3077_; lean_object* v_err_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_res_3065_);
v_pos_3077_ = lean_ctor_get(v___x_3067_, 0);
v_err_3078_ = lean_ctor_get(v___x_3067_, 1);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3067_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_err_3078_);
lean_inc(v_pos_3077_);
lean_dec(v___x_3067_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_pos_3077_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_err_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
return v___x_3063_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3086_){
_start:
{
uint32_t v___x_3087_; uint32_t v___x_3093_; uint8_t v___x_3094_; 
v___x_3087_ = lean_uint8_to_uint32(v_c_3086_);
v___x_3093_ = 33;
v___x_3094_ = lean_uint32_dec_le(v___x_3093_, v___x_3087_);
if (v___x_3094_ == 0)
{
goto v___jp_3088_;
}
else
{
uint32_t v___x_3095_; uint8_t v___x_3096_; 
v___x_3095_ = 126;
v___x_3096_ = lean_uint32_dec_le(v___x_3087_, v___x_3095_);
if (v___x_3096_ == 0)
{
goto v___jp_3088_;
}
else
{
return v___x_3096_;
}
}
v___jp_3088_:
{
uint32_t v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = 32;
v___x_3090_ = lean_uint32_dec_eq(v___x_3087_, v___x_3089_);
if (v___x_3090_ == 0)
{
uint32_t v___x_3091_; uint8_t v___x_3092_; 
v___x_3091_ = 9;
v___x_3092_ = lean_uint32_dec_eq(v___x_3087_, v___x_3091_);
return v___x_3092_;
}
else
{
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3097_){
_start:
{
uint8_t v_c_boxed_3098_; uint8_t v_res_3099_; lean_object* v_r_3100_; 
v_c_boxed_3098_ = lean_unbox(v_c_3097_);
v_res_3099_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3098_);
v_r_3100_ = lean_box(v_res_3099_);
return v_r_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_maxReasonPhraseLength_3103_; lean_object* v___f_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v_snd_3107_; lean_object* v_snd_3108_; uint8_t v___x_3109_; 
v_maxReasonPhraseLength_3103_ = lean_ctor_get(v_limits_3101_, 16);
v___f_3104_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_3105_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3102_);
v___x_3106_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3104_, v_maxReasonPhraseLength_3103_, v___x_3105_, v_a_3102_);
v_snd_3107_ = lean_ctor_get(v___x_3106_, 1);
lean_inc(v_snd_3107_);
v_snd_3108_ = lean_ctor_get(v_snd_3107_, 1);
v___x_3109_ = lean_unbox(v_snd_3108_);
if (v___x_3109_ == 0)
{
lean_object* v_fst_3110_; lean_object* v_fst_3111_; lean_object* v_array_3112_; lean_object* v_idx_3113_; lean_object* v_lower_3115_; lean_object* v_upper_3116_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___y_3128_; uint8_t v___x_3130_; 
v_fst_3110_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_fst_3110_);
lean_dec_ref(v___x_3106_);
v_fst_3111_ = lean_ctor_get(v_snd_3107_, 0);
lean_inc(v_fst_3111_);
lean_dec(v_snd_3107_);
v_array_3112_ = lean_ctor_get(v_a_3102_, 0);
lean_inc_ref(v_array_3112_);
v_idx_3113_ = lean_ctor_get(v_a_3102_, 1);
lean_inc(v_idx_3113_);
lean_dec_ref(v_a_3102_);
v___x_3125_ = lean_nat_add(v_idx_3113_, v_fst_3110_);
lean_dec(v_fst_3110_);
v___x_3126_ = lean_byte_array_size(v_array_3112_);
v___x_3130_ = lean_nat_dec_le(v_idx_3113_, v___x_3105_);
if (v___x_3130_ == 0)
{
v___y_3128_ = v_idx_3113_;
goto v___jp_3127_;
}
else
{
lean_dec(v_idx_3113_);
v___y_3128_ = v___x_3105_;
goto v___jp_3127_;
}
v___jp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3117_ = l_ByteArray_toByteSlice(v_array_3112_, v_lower_3115_, v_upper_3116_);
v___x_3118_ = l_ByteSlice_toByteArray(v___x_3117_);
v___x_3119_ = lean_string_validate_utf8(v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_dec_ref(v___x_3118_);
v___x_3120_ = lean_box(0);
v___x_3121_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3120_, v_fst_3111_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = lean_string_from_utf8_unchecked(v___x_3118_);
v___x_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
v___x_3124_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3123_, v_fst_3111_);
lean_dec_ref_known(v___x_3123_, 1);
return v___x_3124_;
}
}
v___jp_3127_:
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_nat_dec_le(v___x_3125_, v___x_3126_);
if (v___x_3129_ == 0)
{
lean_dec(v___x_3125_);
v_lower_3115_ = v___y_3128_;
v_upper_3116_ = v___x_3126_;
goto v___jp_3114_;
}
else
{
v_lower_3115_ = v___y_3128_;
v_upper_3116_ = v___x_3125_;
goto v___jp_3114_;
}
}
}
else
{
lean_object* v_fst_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___x_3106_);
lean_dec_ref(v_a_3102_);
v_fst_3131_ = lean_ctor_get(v_snd_3107_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_snd_3107_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v_snd_3107_, 1);
lean_dec(v_unused_3140_);
v___x_3133_ = v_snd_3107_;
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_fst_3131_);
lean_dec(v_snd_3107_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = lean_box(0);
if (v_isShared_3134_ == 0)
{
lean_ctor_set_tag(v___x_3133_, 1);
lean_ctor_set(v___x_3133_, 1, v___x_3135_);
v___x_3137_ = v___x_3133_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_fst_3131_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3141_, v_a_3142_);
lean_dec_ref(v_limits_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3144_) == 0)
{
uint8_t v___x_3145_; 
v___x_3145_ = 1;
return v___x_3145_;
}
else
{
lean_object* v_head_3146_; lean_object* v_tail_3147_; uint32_t v___x_3148_; uint32_t v___x_3149_; uint8_t v___x_3150_; 
v_head_3146_ = lean_ctor_get(v_x_3144_, 0);
v_tail_3147_ = lean_ctor_get(v_x_3144_, 1);
v___x_3148_ = 9;
v___x_3149_ = lean_unbox_uint32(v_head_3146_);
v___x_3150_ = lean_uint32_dec_eq(v___x_3149_, v___x_3148_);
if (v___x_3150_ == 0)
{
uint32_t v___x_3151_; uint32_t v___x_3152_; uint8_t v___x_3153_; 
v___x_3151_ = 32;
v___x_3152_ = lean_unbox_uint32(v_head_3146_);
v___x_3153_ = lean_uint32_dec_eq(v___x_3152_, v___x_3151_);
if (v___x_3153_ == 0)
{
uint32_t v___x_3154_; uint32_t v___x_3155_; uint8_t v___x_3156_; 
v___x_3154_ = 33;
v___x_3155_ = lean_unbox_uint32(v_head_3146_);
v___x_3156_ = lean_uint32_dec_le(v___x_3154_, v___x_3155_);
if (v___x_3156_ == 0)
{
return v___x_3156_;
}
else
{
uint32_t v___x_3157_; uint32_t v___x_3158_; uint8_t v___x_3159_; 
v___x_3157_ = 126;
v___x_3158_ = lean_unbox_uint32(v_head_3146_);
v___x_3159_ = lean_uint32_dec_le(v___x_3158_, v___x_3157_);
if (v___x_3159_ == 0)
{
return v___x_3159_;
}
else
{
v_x_3144_ = v_tail_3147_;
goto _start;
}
}
}
else
{
v_x_3144_ = v_tail_3147_;
goto _start;
}
}
else
{
v_x_3144_ = v_tail_3147_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3163_){
_start:
{
uint8_t v_res_3164_; lean_object* v_r_3165_; 
v_res_3164_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3163_);
lean_dec(v_x_3163_);
v_r_3165_ = lean_box(v_res_3164_);
return v_r_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_array_3174_; lean_object* v_idx_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_array_3174_ = lean_ctor_get(v_a_3170_, 0);
v_idx_3175_ = lean_ctor_get(v_a_3170_, 1);
v___x_3176_ = lean_byte_array_size(v_array_3174_);
v___x_3177_ = lean_nat_dec_lt(v_idx_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = lean_box(0);
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v_a_3170_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
return v___x_3179_;
}
else
{
uint8_t v_c_3180_; uint8_t v___x_3181_; uint8_t v___x_3182_; 
v_c_3180_ = lean_byte_array_fget(v_array_3174_, v_idx_3175_);
v___x_3181_ = 48;
v___x_3182_ = lean_uint8_dec_le(v___x_3181_, v_c_3180_);
if (v___x_3182_ == 0)
{
goto v___jp_3171_;
}
else
{
uint8_t v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = 57;
v___x_3184_ = lean_uint8_dec_le(v_c_3180_, v___x_3183_);
if (v___x_3184_ == 0)
{
goto v___jp_3171_;
}
else
{
lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3288_; 
lean_inc(v_idx_3175_);
lean_inc_ref(v_array_3174_);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_a_3170_);
if (v_isSharedCheck_3288_ == 0)
{
lean_object* v_unused_3289_; lean_object* v_unused_3290_; 
v_unused_3289_ = lean_ctor_get(v_a_3170_, 1);
lean_dec(v_unused_3289_);
v_unused_3290_ = lean_ctor_get(v_a_3170_, 0);
lean_dec(v_unused_3290_);
v___x_3186_ = v_a_3170_;
v_isShared_3187_ = v_isSharedCheck_3288_;
goto v_resetjp_3185_;
}
else
{
lean_dec(v_a_3170_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3288_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v_it_x27_3191_; 
v___x_3188_ = lean_unsigned_to_nat(1u);
v___x_3189_ = lean_nat_add(v_idx_3175_, v___x_3188_);
lean_dec(v_idx_3175_);
lean_inc(v___x_3189_);
lean_inc_ref(v_array_3174_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 1, v___x_3189_);
v_it_x27_3191_ = v___x_3186_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_array_3174_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v___x_3189_);
v_it_x27_3191_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_nat_dec_lt(v___x_3189_, v___x_3176_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_dec(v___x_3189_);
lean_dec_ref(v_array_3174_);
v___x_3196_ = lean_box(0);
v___x_3197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_it_x27_3191_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
return v___x_3197_;
}
else
{
uint8_t v_c_3198_; uint8_t v___x_3199_; 
v_c_3198_ = lean_byte_array_fget(v_array_3174_, v___x_3189_);
v___x_3199_ = lean_uint8_dec_le(v___x_3181_, v_c_3198_);
if (v___x_3199_ == 0)
{
lean_dec(v___x_3189_);
lean_dec_ref(v_array_3174_);
goto v___jp_3192_;
}
else
{
uint8_t v___x_3200_; 
v___x_3200_ = lean_uint8_dec_le(v_c_3198_, v___x_3183_);
if (v___x_3200_ == 0)
{
lean_dec(v___x_3189_);
lean_dec_ref(v_array_3174_);
goto v___jp_3192_;
}
else
{
lean_object* v___x_3201_; lean_object* v_it_x27_3202_; uint8_t v___x_3206_; 
lean_dec_ref(v_it_x27_3191_);
v___x_3201_ = lean_nat_add(v___x_3189_, v___x_3188_);
lean_dec(v___x_3189_);
lean_inc(v___x_3201_);
lean_inc_ref(v_array_3174_);
v_it_x27_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3202_, 0, v_array_3174_);
lean_ctor_set(v_it_x27_3202_, 1, v___x_3201_);
v___x_3206_ = lean_nat_dec_lt(v___x_3201_, v___x_3176_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_dec(v___x_3201_);
lean_dec_ref(v_array_3174_);
v___x_3207_ = lean_box(0);
v___x_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3208_, 0, v_it_x27_3202_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
return v___x_3208_;
}
else
{
uint8_t v_c_3209_; uint8_t v___x_3210_; 
v_c_3209_ = lean_byte_array_fget(v_array_3174_, v___x_3201_);
v___x_3210_ = lean_uint8_dec_le(v___x_3181_, v_c_3209_);
if (v___x_3210_ == 0)
{
lean_dec(v___x_3201_);
lean_dec_ref(v_array_3174_);
goto v___jp_3203_;
}
else
{
uint8_t v___x_3211_; 
v___x_3211_ = lean_uint8_dec_le(v_c_3209_, v___x_3183_);
if (v___x_3211_ == 0)
{
lean_dec(v___x_3201_);
lean_dec_ref(v_array_3174_);
goto v___jp_3203_;
}
else
{
lean_object* v___x_3212_; lean_object* v_it_x27_3213_; uint8_t v___x_3214_; 
lean_dec_ref_known(v_it_x27_3202_, 2);
v___x_3212_ = lean_nat_add(v___x_3201_, v___x_3188_);
lean_dec(v___x_3201_);
lean_inc(v___x_3212_);
lean_inc_ref(v_array_3174_);
v_it_x27_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3213_, 0, v_array_3174_);
lean_ctor_set(v_it_x27_3213_, 1, v___x_3212_);
v___x_3214_ = lean_nat_dec_lt(v___x_3212_, v___x_3176_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec(v___x_3212_);
lean_dec_ref(v_array_3174_);
v___x_3215_ = lean_box(0);
v___x_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3216_, 0, v_it_x27_3213_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
return v___x_3216_;
}
else
{
uint8_t v___x_3217_; uint8_t v_got_3218_; uint8_t v___x_3219_; 
v___x_3217_ = 32;
v_got_3218_ = lean_byte_array_fget(v_array_3174_, v___x_3212_);
v___x_3219_ = lean_uint8_dec_eq(v_got_3218_, v___x_3217_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec(v___x_3212_);
lean_dec_ref(v_array_3174_);
v___x_3220_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_it_x27_3213_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
lean_dec_ref_known(v_it_x27_3213_, 2);
v___x_3222_ = lean_nat_add(v___x_3212_, v___x_3188_);
lean_dec(v___x_3212_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v_array_3174_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3169_, v___x_3223_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_pos_3225_; lean_object* v_res_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3277_; 
v_pos_3225_ = lean_ctor_get(v___x_3224_, 0);
v_res_3226_ = lean_ctor_get(v___x_3224_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3228_ = v___x_3224_;
v_isShared_3229_ = v_isSharedCheck_3277_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_res_3226_);
lean_inc(v_pos_3225_);
lean_dec(v___x_3224_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3277_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3231_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3230_, v_pos_3225_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_pos_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3266_; 
v_pos_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v___x_3231_, 1);
lean_dec(v_unused_3267_);
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3266_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_pos_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3266_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3241_; uint8_t v___x_3242_; 
lean_inc(v_res_3226_);
v___x_3241_ = l_String_toListImpl(v_res_3226_);
v___x_3242_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3241_);
lean_dec(v___x_3241_);
if (v___x_3242_ == 0)
{
lean_del_object(v___x_3228_);
lean_dec(v_res_3226_);
goto v___jp_3236_;
}
else
{
lean_object* v___x_3243_; uint32_t v___x_3244_; uint32_t v___x_3245_; uint32_t v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; uint16_t v___x_3260_; lean_object* v___x_3261_; 
v___x_3243_ = lean_unsigned_to_nat(48u);
v___x_3244_ = lean_uint8_to_uint32(v_c_3180_);
v___x_3245_ = lean_uint8_to_uint32(v_c_3198_);
v___x_3246_ = lean_uint8_to_uint32(v_c_3209_);
v___x_3247_ = lean_uint32_to_nat(v___x_3244_);
v___x_3248_ = lean_nat_sub(v___x_3247_, v___x_3243_);
lean_dec(v___x_3247_);
v___x_3249_ = lean_unsigned_to_nat(100u);
v___x_3250_ = lean_nat_mul(v___x_3248_, v___x_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_uint32_to_nat(v___x_3245_);
v___x_3252_ = lean_nat_sub(v___x_3251_, v___x_3243_);
lean_dec(v___x_3251_);
v___x_3253_ = lean_unsigned_to_nat(10u);
v___x_3254_ = lean_nat_mul(v___x_3252_, v___x_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_nat_add(v___x_3250_, v___x_3254_);
lean_dec(v___x_3254_);
lean_dec(v___x_3250_);
v___x_3256_ = lean_uint32_to_nat(v___x_3246_);
v___x_3257_ = lean_nat_sub(v___x_3256_, v___x_3243_);
lean_dec(v___x_3256_);
v___x_3258_ = lean_nat_add(v___x_3255_, v___x_3257_);
lean_dec(v___x_3257_);
lean_dec(v___x_3255_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_res_3226_);
v___x_3260_ = lean_uint16_of_nat(v___x_3258_);
lean_dec(v___x_3258_);
v___x_3261_ = l_Std_Http_Status_ofCode(v___x_3259_, v___x_3260_);
if (lean_obj_tag(v___x_3261_) == 1)
{
lean_object* v_val_3262_; lean_object* v___x_3264_; 
lean_del_object(v___x_3234_);
v_val_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_val_3262_);
lean_dec_ref_known(v___x_3261_, 1);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v_val_3262_);
lean_ctor_set(v___x_3228_, 0, v_pos_3232_);
v___x_3264_ = v___x_3228_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_pos_3232_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_val_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
else
{
lean_dec(v___x_3261_);
lean_del_object(v___x_3228_);
goto v___jp_3236_;
}
}
v___jp_3236_:
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3237_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
if (v_isShared_3235_ == 0)
{
lean_ctor_set_tag(v___x_3234_, 1);
lean_ctor_set(v___x_3234_, 1, v___x_3237_);
v___x_3239_ = v___x_3234_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_pos_3232_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_pos_3268_; lean_object* v_err_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_del_object(v___x_3228_);
lean_dec(v_res_3226_);
v_pos_3268_ = lean_ctor_get(v___x_3231_, 0);
v_err_3269_ = lean_ctor_get(v___x_3231_, 1);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3231_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_err_3269_);
lean_inc(v_pos_3268_);
lean_dec(v___x_3231_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_pos_3268_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_err_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
else
{
lean_object* v_pos_3278_; lean_object* v_err_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
v_pos_3278_ = lean_ctor_get(v___x_3224_, 0);
v_err_3279_ = lean_ctor_get(v___x_3224_, 1);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3224_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_err_3279_);
lean_inc(v_pos_3278_);
lean_dec(v___x_3224_);
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
}
}
}
}
v___jp_3203_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3205_, 0, v_it_x27_3202_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
return v___x_3205_;
}
}
}
}
v___jp_3192_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3194_, 0, v_it_x27_3191_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
return v___x_3194_;
}
}
}
}
}
}
v___jp_3171_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3173_, 0, v_a_3170_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3291_, v_a_3292_);
lean_dec_ref(v_limits_3291_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3295_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_pos_3297_; lean_object* v_res_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3372_; 
v_pos_3297_ = lean_ctor_get(v___x_3296_, 0);
v_res_3298_ = lean_ctor_get(v___x_3296_, 1);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3300_ = v___x_3296_;
v_isShared_3301_ = v_isSharedCheck_3372_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_res_3298_);
lean_inc(v_pos_3297_);
lean_dec(v___x_3296_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3372_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v_array_3302_; lean_object* v_idx_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_array_3302_ = lean_ctor_get(v_pos_3297_, 0);
v_idx_3303_ = lean_ctor_get(v_pos_3297_, 1);
v___x_3304_ = lean_byte_array_size(v_array_3302_);
v___x_3305_ = lean_nat_dec_lt(v_idx_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_dec(v_res_3298_);
v___x_3306_ = lean_box(0);
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 1);
lean_ctor_set(v___x_3300_, 1, v___x_3306_);
v___x_3308_ = v___x_3300_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_pos_3297_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
else
{
uint8_t v___x_3310_; uint8_t v_got_3311_; uint8_t v___x_3312_; 
v___x_3310_ = 32;
v_got_3311_ = lean_byte_array_fget(v_array_3302_, v_idx_3303_);
v___x_3312_ = lean_uint8_dec_eq(v_got_3311_, v___x_3310_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
lean_dec(v_res_3298_);
v___x_3313_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 1);
lean_ctor_set(v___x_3300_, 1, v___x_3313_);
v___x_3315_ = v___x_3300_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_pos_3297_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
else
{
lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3369_; 
lean_inc(v_idx_3303_);
lean_inc_ref(v_array_3302_);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_pos_3297_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; lean_object* v_unused_3371_; 
v_unused_3370_ = lean_ctor_get(v_pos_3297_, 1);
lean_dec(v_unused_3370_);
v_unused_3371_ = lean_ctor_get(v_pos_3297_, 0);
lean_dec(v_unused_3371_);
v___x_3318_ = v_pos_3297_;
v_isShared_3319_ = v_isSharedCheck_3369_;
goto v_resetjp_3317_;
}
else
{
lean_dec(v_pos_3297_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3369_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_fst_3320_; lean_object* v_snd_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3368_; 
v_fst_3320_ = lean_ctor_get(v_res_3298_, 0);
v_snd_3321_ = lean_ctor_get(v_res_3298_, 1);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_res_3298_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3323_ = v_res_3298_;
v_isShared_3324_ = v_isSharedCheck_3368_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_snd_3321_);
lean_inc(v_fst_3320_);
lean_dec(v_res_3298_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3368_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3325_ = lean_unsigned_to_nat(1u);
v___x_3326_ = lean_nat_add(v_idx_3303_, v___x_3325_);
lean_dec(v_idx_3303_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 1, v___x_3326_);
v___x_3328_ = v___x_3318_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_array_3302_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3329_; 
v___x_3329_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3294_, v___x_3328_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_pos_3330_; lean_object* v_res_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3357_; 
v_pos_3330_ = lean_ctor_get(v___x_3329_, 0);
v_res_3331_ = lean_ctor_get(v___x_3329_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3333_ = v___x_3329_;
v_isShared_3334_ = v_isSharedCheck_3357_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_res_3331_);
lean_inc(v_pos_3330_);
lean_dec(v___x_3329_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3357_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_nat_dec_eq(v_fst_3320_, v___x_3325_);
lean_dec(v_fst_3320_);
if (v___x_3340_ == 0)
{
lean_del_object(v___x_3323_);
goto v___jp_3341_;
}
else
{
uint8_t v___x_3350_; 
v___x_3350_ = lean_nat_dec_eq(v_snd_3321_, v___x_3325_);
if (v___x_3350_ == 0)
{
lean_del_object(v___x_3323_);
goto v___jp_3341_;
}
else
{
uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
lean_del_object(v___x_3333_);
lean_dec(v_snd_3321_);
lean_del_object(v___x_3300_);
v___x_3351_ = 1;
v___x_3352_ = l_Std_Http_Headers_empty;
v___x_3353_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3353_, 0, v_res_3331_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*2, v___x_3351_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 1, v___x_3353_);
lean_ctor_set(v___x_3323_, 0, v_pos_3330_);
v___x_3355_ = v___x_3323_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_pos_3330_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
v___jp_3335_:
{
lean_object* v___x_3336_; lean_object* v___x_3338_; 
v___x_3336_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_3334_ == 0)
{
lean_ctor_set_tag(v___x_3333_, 1);
lean_ctor_set(v___x_3333_, 1, v___x_3336_);
v___x_3338_ = v___x_3333_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_pos_3330_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
v___jp_3341_:
{
if (v___x_3340_ == 0)
{
lean_dec(v_res_3331_);
lean_dec(v_snd_3321_);
lean_del_object(v___x_3300_);
goto v___jp_3335_;
}
else
{
lean_object* v___x_3342_; uint8_t v___x_3343_; 
v___x_3342_ = lean_unsigned_to_nat(0u);
v___x_3343_ = lean_nat_dec_eq(v_snd_3321_, v___x_3342_);
lean_dec(v_snd_3321_);
if (v___x_3343_ == 0)
{
lean_dec(v_res_3331_);
lean_del_object(v___x_3300_);
goto v___jp_3335_;
}
else
{
uint8_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
lean_del_object(v___x_3333_);
v___x_3344_ = 0;
v___x_3345_ = l_Std_Http_Headers_empty;
v___x_3346_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3346_, 0, v_res_3331_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*2, v___x_3344_);
if (v_isShared_3301_ == 0)
{
lean_ctor_set(v___x_3300_, 1, v___x_3346_);
lean_ctor_set(v___x_3300_, 0, v_pos_3330_);
v___x_3348_ = v___x_3300_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_pos_3330_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3358_; lean_object* v_err_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_del_object(v___x_3323_);
lean_dec(v_snd_3321_);
lean_dec(v_fst_3320_);
lean_del_object(v___x_3300_);
v_pos_3358_ = lean_ctor_get(v___x_3329_, 0);
v_err_3359_ = lean_ctor_get(v___x_3329_, 1);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3329_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_err_3359_);
lean_inc(v_pos_3358_);
lean_dec(v___x_3329_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_pos_3358_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_err_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
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
lean_object* v_pos_3373_; lean_object* v_err_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
v_pos_3373_ = lean_ctor_get(v___x_3296_, 0);
v_err_3374_ = lean_ctor_get(v___x_3296_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3296_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_err_3374_);
lean_inc(v_pos_3373_);
lean_dec(v___x_3296_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_pos_3373_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_err_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_3382_, v_a_3383_);
lean_dec_ref(v_limits_3382_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3386_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_pos_3388_; lean_object* v_res_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3448_; 
v_pos_3388_ = lean_ctor_get(v___x_3387_, 0);
v_res_3389_ = lean_ctor_get(v___x_3387_, 1);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3391_ = v___x_3387_;
v_isShared_3392_ = v_isSharedCheck_3448_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_res_3389_);
lean_inc(v_pos_3388_);
lean_dec(v___x_3387_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3448_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_array_3393_; lean_object* v_idx_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v_array_3393_ = lean_ctor_get(v_pos_3388_, 0);
v_idx_3394_ = lean_ctor_get(v_pos_3388_, 1);
v___x_3395_ = lean_byte_array_size(v_array_3393_);
v___x_3396_ = lean_nat_dec_lt(v_idx_3394_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3399_; 
lean_dec(v_res_3389_);
v___x_3397_ = lean_box(0);
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 1);
lean_ctor_set(v___x_3391_, 1, v___x_3397_);
v___x_3399_ = v___x_3391_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_pos_3388_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
else
{
uint8_t v___x_3401_; uint8_t v_got_3402_; uint8_t v___x_3403_; 
v___x_3401_ = 32;
v_got_3402_ = lean_byte_array_fget(v_array_3393_, v_idx_3394_);
v___x_3403_ = lean_uint8_dec_eq(v_got_3402_, v___x_3401_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
lean_dec(v_res_3389_);
v___x_3404_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 1);
lean_ctor_set(v___x_3391_, 1, v___x_3404_);
v___x_3406_ = v___x_3391_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_pos_3388_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
else
{
lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3445_; 
lean_inc(v_idx_3394_);
lean_inc_ref(v_array_3393_);
lean_del_object(v___x_3391_);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_pos_3388_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; lean_object* v_unused_3447_; 
v_unused_3446_ = lean_ctor_get(v_pos_3388_, 1);
lean_dec(v_unused_3446_);
v_unused_3447_ = lean_ctor_get(v_pos_3388_, 0);
lean_dec(v_unused_3447_);
v___x_3409_ = v_pos_3388_;
v_isShared_3410_ = v_isSharedCheck_3445_;
goto v_resetjp_3408_;
}
else
{
lean_dec(v_pos_3388_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3445_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v_fst_3411_; lean_object* v_snd_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3444_; 
v_fst_3411_ = lean_ctor_get(v_res_3389_, 0);
v_snd_3412_ = lean_ctor_get(v_res_3389_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_res_3389_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3414_ = v_res_3389_;
v_isShared_3415_ = v_isSharedCheck_3444_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_snd_3412_);
lean_inc(v_fst_3411_);
lean_dec(v_res_3389_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3444_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3416_ = lean_unsigned_to_nat(1u);
v___x_3417_ = lean_nat_add(v_idx_3394_, v___x_3416_);
lean_dec(v_idx_3394_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 1, v___x_3417_);
v___x_3419_ = v___x_3409_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_array_3393_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; 
v___x_3420_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3385_, v___x_3419_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_pos_3421_; lean_object* v_res_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3433_; 
v_pos_3421_ = lean_ctor_get(v___x_3420_, 0);
v_res_3422_ = lean_ctor_get(v___x_3420_, 1);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3424_ = v___x_3420_;
v_isShared_3425_ = v_isSharedCheck_3433_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_res_3422_);
lean_inc(v_pos_3421_);
lean_dec(v___x_3420_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3433_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
v___x_3426_ = l_Std_Http_Version_ofNumber_x3f(v_fst_3411_, v_snd_3412_);
lean_dec(v_snd_3412_);
lean_dec(v_fst_3411_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 1, v___x_3426_);
lean_ctor_set(v___x_3414_, 0, v_res_3422_);
v___x_3428_ = v___x_3414_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_res_3422_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3428_);
v___x_3430_ = v___x_3424_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_pos_3421_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
else
{
lean_object* v_pos_3434_; lean_object* v_err_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_del_object(v___x_3414_);
lean_dec(v_snd_3412_);
lean_dec(v_fst_3411_);
v_pos_3434_ = lean_ctor_get(v___x_3420_, 0);
v_err_3435_ = lean_ctor_get(v___x_3420_, 1);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3420_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_err_3435_);
lean_inc(v_pos_3434_);
lean_dec(v___x_3420_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_pos_3434_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_err_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
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
lean_object* v_pos_3449_; lean_object* v_err_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
v_pos_3449_ = lean_ctor_get(v___x_3387_, 0);
v_err_3450_ = lean_ctor_get(v___x_3387_, 1);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3387_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_err_3450_);
lean_inc(v_pos_3449_);
lean_dec(v___x_3387_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_pos_3449_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_err_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_3458_, v_a_3459_);
lean_dec_ref(v_limits_3458_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object* v_limits_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v_maxTrailerHeaders_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v_maxTrailerHeaders_3463_ = lean_ctor_get(v_limits_3461_, 17);
lean_inc(v_maxTrailerHeaders_3463_);
v___x_3464_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3464_, 0, v_limits_3461_);
v___x_3465_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3464_, v_maxTrailerHeaders_3463_, v_a_3462_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_pos_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_pos_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_pos_3466_);
lean_dec_ref_known(v___x_3465_, 2);
v___x_3467_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3468_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3467_, v_pos_3466_);
return v___x_3468_;
}
else
{
lean_object* v_pos_3469_; lean_object* v_err_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
v_pos_3469_ = lean_ctor_get(v___x_3465_, 0);
v_err_3470_ = lean_ctor_get(v___x_3465_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3465_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_err_3470_);
lean_inc(v_pos_3469_);
lean_dec(v___x_3465_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_pos_3469_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_err_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
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
