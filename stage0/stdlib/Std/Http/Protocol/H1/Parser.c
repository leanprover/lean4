// Lean compiler output
// Module: Std.Http.Protocol.H1.Parser
// Imports: public import Std.Internal.Parsec public import Std.Http.Data public import Std.Internal.Parsec.ByteArray public import Std.Http.Protocol.H1.Config import Init.Data.String.Lossy
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_String_toListImpl(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1_value;
static const lean_closure_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '58'"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value;
static const lean_ctor_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3_value)}};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4_value;
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
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "content-length"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "transfer-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "connection"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "te"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "upgrade"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trailer"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6_value;
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___boxed(lean_object*);
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expect"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "authorization"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "max-forwards"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cache-control"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3_value;
static const lean_string_object l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "content-encoding"};
static const lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4_value;
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "forbidden trailer field: "};
static const lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint32_t v___x_10_; uint8_t v___x_11_; 
v___x_2_ = lean_uint8_to_uint32(v_c_1_);
v___x_10_ = 33;
v___x_11_ = lean_uint32_dec_le(v___x_10_, v___x_2_);
if (v___x_11_ == 0)
{
goto v___jp_3_;
}
else
{
uint32_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 126;
v___x_13_ = lean_uint32_dec_le(v___x_2_, v___x_12_);
if (v___x_13_ == 0)
{
goto v___jp_3_;
}
else
{
return v___x_13_;
}
}
v___jp_3_:
{
uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 128;
v___x_5_ = lean_uint32_dec_le(v___x_4_, v___x_2_);
if (v___x_5_ == 0)
{
uint32_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 32;
v___x_7_ = lean_uint32_dec_eq(v___x_2_, v___x_6_);
if (v___x_7_ == 0)
{
uint32_t v___x_8_; uint8_t v___x_9_; 
v___x_8_ = 9;
v___x_9_ = lean_uint32_dec_eq(v___x_2_, v___x_8_);
return v___x_9_;
}
else
{
return v___x_7_;
}
}
else
{
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar___boxed(lean_object* v_c_14_){
_start:
{
uint8_t v_c_boxed_15_; uint8_t v_res_16_; lean_object* v_r_17_; 
v_c_boxed_15_ = lean_unbox(v_c_14_);
v_res_16_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(v_c_boxed_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t v_c_18_){
_start:
{
uint32_t v___x_19_; uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_19_ = lean_uint8_to_uint32(v_c_18_);
v___x_25_ = 9;
v___x_26_ = lean_uint32_dec_eq(v___x_19_, v___x_25_);
if (v___x_26_ == 0)
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 32;
v___x_28_ = lean_uint32_dec_eq(v___x_19_, v___x_27_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 33;
v___x_30_ = lean_uint32_dec_eq(v___x_19_, v___x_29_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 35;
v___x_32_ = lean_uint32_dec_le(v___x_31_, v___x_19_);
if (v___x_32_ == 0)
{
goto v___jp_20_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 91;
v___x_34_ = lean_uint32_dec_le(v___x_19_, v___x_33_);
if (v___x_34_ == 0)
{
goto v___jp_20_;
}
else
{
return v___x_34_;
}
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
v___jp_20_:
{
uint32_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 93;
v___x_22_ = lean_uint32_dec_le(v___x_21_, v___x_19_);
if (v___x_22_ == 0)
{
return v___x_22_;
}
else
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 126;
v___x_24_ = lean_uint32_dec_le(v___x_19_, v___x_23_);
return v___x_24_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof___redArg(lean_object* v_p_49_, lean_object* v_it_50_){
_start:
{
lean_object* v___x_51_; 
lean_inc_ref(v_it_50_);
v___x_51_ = lean_apply_1(v_p_49_, v_it_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_pos_52_; lean_object* v_res_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_61_; 
lean_dec_ref(v_it_50_);
v_pos_52_ = lean_ctor_get(v___x_51_, 0);
v_res_53_ = lean_ctor_get(v___x_51_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_61_ == 0)
{
v___x_55_ = v___x_51_;
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_res_53_);
lean_inc(v_pos_52_);
lean_dec(v___x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v_res_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_pos_52_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
else
{
lean_object* v_err_62_; 
v_err_62_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_err_62_);
if (lean_obj_tag(v_err_62_) == 0)
{
lean_object* v_pos_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
lean_dec_ref(v_it_50_);
v_pos_63_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_70_ == 0)
{
lean_object* v_unused_71_; 
v_unused_71_ = lean_ctor_get(v___x_51_, 1);
lean_dec(v_unused_71_);
v___x_65_ = v___x_51_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_pos_63_);
lean_dec(v___x_51_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_pos_63_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_err_62_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
else
{
lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_79_; 
lean_dec(v_err_62_);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; lean_object* v_unused_81_; 
v_unused_80_ = lean_ctor_get(v___x_51_, 1);
lean_dec(v_unused_80_);
v_unused_81_ = lean_ctor_get(v___x_51_, 0);
lean_dec(v_unused_81_);
v___x_73_ = v___x_51_;
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
else
{
lean_dec(v___x_51_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = lean_box(0);
if (v_isShared_74_ == 0)
{
lean_ctor_set_tag(v___x_73_, 0);
lean_ctor_set(v___x_73_, 1, v___x_75_);
lean_ctor_set(v___x_73_, 0, v_it_50_);
v___x_77_ = v___x_73_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_it_50_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_optionalUnlessEof(lean_object* v_00_u03b1_82_, lean_object* v_p_83_, lean_object* v_it_84_){
_start:
{
lean_object* v___x_85_; 
lean_inc_ref(v_it_84_);
v___x_85_ = lean_apply_1(v_p_83_, v_it_84_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_pos_86_; lean_object* v_res_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
lean_dec_ref(v_it_84_);
v_pos_86_ = lean_ctor_get(v___x_85_, 0);
v_res_87_ = lean_ctor_get(v___x_85_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v___x_85_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_res_87_);
lean_inc(v_pos_86_);
lean_dec(v___x_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_res_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_pos_86_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_err_96_; 
v_err_96_ = lean_ctor_get(v___x_85_, 1);
lean_inc(v_err_96_);
if (lean_obj_tag(v_err_96_) == 0)
{
lean_object* v_pos_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec_ref(v_it_84_);
v_pos_97_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_85_, 1);
lean_dec(v_unused_105_);
v___x_99_ = v___x_85_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_pos_97_);
lean_dec(v___x_85_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_pos_97_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_err_96_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_err_96_);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; lean_object* v_unused_115_; 
v_unused_114_ = lean_ctor_get(v___x_85_, 1);
lean_dec(v_unused_114_);
v_unused_115_ = lean_ctor_get(v___x_85_, 0);
lean_dec(v_unused_115_);
v___x_107_ = v___x_85_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_dec(v___x_85_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = lean_box(0);
if (v_isShared_108_ == 0)
{
lean_ctor_set_tag(v___x_107_, 0);
lean_ctor_set(v___x_107_, 1, v___x_109_);
lean_ctor_set(v___x_107_, 0, v_it_84_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_it_84_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object* v_parser_118_, lean_object* v_maxCount_119_, lean_object* v_acc_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; 
lean_inc_ref(v_parser_118_);
lean_inc_ref(v_a_121_);
v___x_122_ = lean_apply_1(v_parser_118_, v_a_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_res_123_; 
v_res_123_ = lean_ctor_get(v___x_122_, 1);
lean_inc(v_res_123_);
if (lean_obj_tag(v_res_123_) == 0)
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_maxCount_119_);
lean_dec_ref(v_parser_118_);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; lean_object* v_unused_132_; 
v_unused_131_ = lean_ctor_get(v___x_122_, 1);
lean_dec(v_unused_131_);
v_unused_132_ = lean_ctor_get(v___x_122_, 0);
lean_dec(v_unused_132_);
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v_acc_120_);
lean_ctor_set(v___x_125_, 0, v_a_121_);
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_121_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_acc_120_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_pos_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v_a_121_);
v_pos_133_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v___x_122_, 1);
lean_dec(v_unused_162_);
v___x_135_ = v___x_122_;
v_isShared_136_ = v_isSharedCheck_161_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_pos_133_);
lean_dec(v___x_122_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_161_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_val_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_160_; 
v_val_137_ = lean_ctor_get(v_res_123_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_res_123_);
if (v_isSharedCheck_160_ == 0)
{
v___x_139_ = v_res_123_;
v_isShared_140_ = v_isSharedCheck_160_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_val_137_);
lean_dec(v_res_123_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_160_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_141_ = lean_array_get_size(v_acc_120_);
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_nat_add(v___x_141_, v___x_142_);
v___x_144_ = lean_nat_dec_lt(v_maxCount_119_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
lean_dec(v___x_143_);
lean_del_object(v___x_139_);
lean_del_object(v___x_135_);
v___x_145_ = lean_array_push(v_acc_120_, v_val_137_);
v_acc_120_ = v___x_145_;
v_a_121_ = v_pos_133_;
goto _start;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
lean_dec(v_val_137_);
lean_dec_ref(v_acc_120_);
lean_dec_ref(v_parser_118_);
v___x_147_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__0));
v___x_148_ = l_Nat_reprFast(v___x_143_);
v___x_149_ = lean_string_append(v___x_147_, v___x_148_);
lean_dec_ref(v___x_148_);
v___x_150_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1));
v___x_151_ = lean_string_append(v___x_149_, v___x_150_);
v___x_152_ = l_Nat_reprFast(v_maxCount_119_);
v___x_153_ = lean_string_append(v___x_151_, v___x_152_);
lean_dec_ref(v___x_152_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_153_);
v___x_155_ = v___x_139_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_159_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_157_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 1);
lean_ctor_set(v___x_135_, 1, v___x_155_);
v___x_157_ = v___x_135_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_pos_133_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
}
else
{
lean_object* v_err_163_; 
lean_dec(v_maxCount_119_);
lean_dec_ref(v_parser_118_);
v_err_163_ = lean_ctor_get(v___x_122_, 1);
lean_inc(v_err_163_);
if (lean_obj_tag(v_err_163_) == 0)
{
lean_object* v_pos_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec_ref(v_a_121_);
lean_dec_ref(v_acc_120_);
v_pos_164_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; 
v_unused_172_ = lean_ctor_get(v___x_122_, 1);
lean_dec(v_unused_172_);
v___x_166_ = v___x_122_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_pos_164_);
lean_dec(v___x_122_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_pos_164_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_err_163_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_err_163_);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; lean_object* v_unused_181_; 
v_unused_180_ = lean_ctor_get(v___x_122_, 1);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v___x_122_, 0);
lean_dec(v_unused_181_);
v___x_174_ = v___x_122_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_dec(v___x_122_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set_tag(v___x_174_, 0);
lean_ctor_set(v___x_174_, 1, v_acc_120_);
lean_ctor_set(v___x_174_, 0, v_a_121_);
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_121_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_acc_120_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object* v_00_u03b1_182_, lean_object* v_parser_183_, lean_object* v_maxCount_184_, lean_object* v_acc_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_183_, v_maxCount_184_, v_acc_185_, v_a_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go_match__1_splitter___redArg(lean_object* v_____do__lift_188_, lean_object* v_h__1_189_, lean_object* v_h__2_190_){
_start:
{
if (lean_obj_tag(v_____do__lift_188_) == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_h__2_190_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_apply_1(v_h__1_189_, v___x_191_);
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; 
lean_dec(v_h__1_189_);
v_val_193_ = lean_ctor_get(v_____do__lift_188_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v_____do__lift_188_, 1);
v___x_194_ = lean_apply_1(v_h__2_190_, v_val_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go_match__1_splitter(lean_object* v_00_u03b1_195_, lean_object* v_motive_196_, lean_object* v_____do__lift_197_, lean_object* v_h__1_198_, lean_object* v_h__2_199_){
_start:
{
if (lean_obj_tag(v_____do__lift_197_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_h__2_199_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_apply_1(v_h__1_198_, v___x_200_);
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_203_; 
lean_dec(v_h__1_198_);
v_val_202_ = lean_ctor_get(v_____do__lift_197_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v_____do__lift_197_, 1);
v___x_203_ = lean_apply_1(v_h__2_199_, v_val_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object* v_parser_206_, lean_object* v_maxCount_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0));
v___x_210_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_206_, v_maxCount_207_, v___x_209_, v_a_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object* v_00_u03b1_211_, lean_object* v_parser_212_, lean_object* v_maxCount_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v_parser_212_, v_maxCount_213_, v_a_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object* v_x_219_, lean_object* v_a_220_){
_start:
{
if (lean_obj_tag(v_x_219_) == 1)
{
lean_object* v_val_221_; lean_object* v___x_222_; 
v_val_221_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_val_221_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_a_220_);
lean_ctor_set(v___x_222_, 1, v_val_221_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1));
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v_a_220_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object* v_x_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_225_, v_a_226_);
lean_dec(v_x_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object* v_00_u03b1_228_, lean_object* v_x_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_229_, v_a_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object* v_00_u03b1_232_, lean_object* v_x_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(v_00_u03b1_232_, v_x_233_, v_a_234_);
lean_dec(v_x_233_);
return v_res_235_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t v_c_236_){
_start:
{
uint32_t v___x_237_; uint32_t v___x_248_; uint8_t v___x_249_; 
v___x_237_ = lean_uint8_to_uint32(v_c_236_);
v___x_248_ = 33;
v___x_249_ = lean_uint32_dec_eq(v___x_237_, v___x_248_);
if (v___x_249_ == 0)
{
uint32_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 35;
v___x_251_ = lean_uint32_dec_eq(v___x_237_, v___x_250_);
if (v___x_251_ == 0)
{
uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_252_ = 36;
v___x_253_ = lean_uint32_dec_eq(v___x_237_, v___x_252_);
if (v___x_253_ == 0)
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 37;
v___x_255_ = lean_uint32_dec_eq(v___x_237_, v___x_254_);
if (v___x_255_ == 0)
{
uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 38;
v___x_257_ = lean_uint32_dec_eq(v___x_237_, v___x_256_);
if (v___x_257_ == 0)
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 39;
v___x_259_ = lean_uint32_dec_eq(v___x_237_, v___x_258_);
if (v___x_259_ == 0)
{
uint32_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = 42;
v___x_261_ = lean_uint32_dec_eq(v___x_237_, v___x_260_);
if (v___x_261_ == 0)
{
uint32_t v___x_262_; uint8_t v___x_263_; 
v___x_262_ = 43;
v___x_263_ = lean_uint32_dec_eq(v___x_237_, v___x_262_);
if (v___x_263_ == 0)
{
uint32_t v___x_264_; uint8_t v___x_265_; 
v___x_264_ = 45;
v___x_265_ = lean_uint32_dec_eq(v___x_237_, v___x_264_);
if (v___x_265_ == 0)
{
uint32_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = 46;
v___x_267_ = lean_uint32_dec_eq(v___x_237_, v___x_266_);
if (v___x_267_ == 0)
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 94;
v___x_269_ = lean_uint32_dec_eq(v___x_237_, v___x_268_);
if (v___x_269_ == 0)
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 95;
v___x_271_ = lean_uint32_dec_eq(v___x_237_, v___x_270_);
if (v___x_271_ == 0)
{
uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 96;
v___x_273_ = lean_uint32_dec_eq(v___x_237_, v___x_272_);
if (v___x_273_ == 0)
{
uint32_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 124;
v___x_275_ = lean_uint32_dec_eq(v___x_237_, v___x_274_);
if (v___x_275_ == 0)
{
uint32_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = 126;
v___x_277_ = lean_uint32_dec_eq(v___x_237_, v___x_276_);
if (v___x_277_ == 0)
{
uint32_t v___x_278_; uint8_t v___x_279_; 
v___x_278_ = 48;
v___x_279_ = lean_uint32_dec_le(v___x_278_, v___x_237_);
if (v___x_279_ == 0)
{
goto v___jp_243_;
}
else
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 57;
v___x_281_ = lean_uint32_dec_le(v___x_237_, v___x_280_);
if (v___x_281_ == 0)
{
goto v___jp_243_;
}
else
{
return v___x_281_;
}
}
}
else
{
return v___x_277_;
}
}
else
{
return v___x_275_;
}
}
else
{
return v___x_273_;
}
}
else
{
return v___x_271_;
}
}
else
{
return v___x_269_;
}
}
else
{
return v___x_267_;
}
}
else
{
return v___x_265_;
}
}
else
{
return v___x_263_;
}
}
else
{
return v___x_261_;
}
}
else
{
return v___x_259_;
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
v___jp_238_:
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 97;
v___x_240_ = lean_uint32_dec_le(v___x_239_, v___x_237_);
if (v___x_240_ == 0)
{
return v___x_240_;
}
else
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 122;
v___x_242_ = lean_uint32_dec_le(v___x_237_, v___x_241_);
return v___x_242_;
}
}
v___jp_243_:
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 65;
v___x_245_ = lean_uint32_dec_le(v___x_244_, v___x_237_);
if (v___x_245_ == 0)
{
goto v___jp_238_;
}
else
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 90;
v___x_247_ = lean_uint32_dec_le(v___x_237_, v___x_246_);
if (v___x_247_ == 0)
{
goto v___jp_238_;
}
else
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object* v_c_282_){
_start:
{
uint8_t v_c_boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_c_boxed_283_ = lean_unbox(v_c_282_);
v_res_284_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_boxed_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object* v_limit_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_snd_295_; lean_object* v_snd_296_; uint8_t v___x_297_; 
v___f_292_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_293_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_291_);
v___x_294_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_292_, v_limit_290_, v___x_293_, v_a_291_);
v_snd_295_ = lean_ctor_get(v___x_294_, 1);
lean_inc(v_snd_295_);
v_snd_296_ = lean_ctor_get(v_snd_295_, 1);
v___x_297_ = lean_unbox(v_snd_296_);
if (v___x_297_ == 0)
{
lean_object* v_fst_298_; lean_object* v_fst_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_327_; 
v_fst_298_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_fst_298_);
lean_dec_ref(v___x_294_);
v_fst_299_ = lean_ctor_get(v_snd_295_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_snd_295_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v_snd_295_, 1);
lean_dec(v_unused_328_);
v___x_301_ = v_snd_295_;
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_fst_299_);
lean_dec(v_snd_295_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_eq(v_fst_298_, v___x_293_);
if (v___x_303_ == 0)
{
lean_object* v_array_304_; lean_object* v_idx_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_322_; 
lean_del_object(v___x_301_);
v_array_304_ = lean_ctor_get(v_a_291_, 0);
v_idx_305_ = lean_ctor_get(v_a_291_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_322_ == 0)
{
v___x_307_ = v_a_291_;
v_isShared_308_ = v_isSharedCheck_322_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_idx_305_);
lean_inc(v_array_304_);
lean_dec(v_a_291_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_322_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_lower_310_; lean_object* v_upper_311_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___y_319_; uint8_t v___x_321_; 
v___x_316_ = lean_nat_add(v_idx_305_, v_fst_298_);
lean_dec(v_fst_298_);
v___x_317_ = lean_byte_array_size(v_array_304_);
v___x_321_ = lean_nat_dec_le(v_idx_305_, v___x_293_);
if (v___x_321_ == 0)
{
v___y_319_ = v_idx_305_;
goto v___jp_318_;
}
else
{
lean_dec(v_idx_305_);
v___y_319_ = v___x_293_;
goto v___jp_318_;
}
v___jp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = l_ByteArray_toByteSlice(v_array_304_, v_lower_310_, v_upper_311_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_312_);
lean_ctor_set(v___x_307_, 0, v_fst_299_);
v___x_314_ = v___x_307_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_fst_299_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
v___jp_318_:
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_le(v___x_316_, v___x_317_);
if (v___x_320_ == 0)
{
lean_dec(v___x_316_);
v_lower_310_ = v___y_319_;
v_upper_311_ = v___x_317_;
goto v___jp_309_;
}
else
{
v_lower_310_ = v___y_319_;
v_upper_311_ = v___x_316_;
goto v___jp_309_;
}
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec(v_fst_299_);
lean_dec(v_fst_298_);
v___x_323_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 1);
lean_ctor_set(v___x_301_, 1, v___x_323_);
lean_ctor_set(v___x_301_, 0, v_a_291_);
v___x_325_ = v___x_301_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_291_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v_fst_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v___x_294_);
lean_dec_ref(v_a_291_);
v_fst_329_ = lean_ctor_get(v_snd_295_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_snd_295_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_snd_295_, 1);
lean_dec(v_unused_338_);
v___x_331_ = v_snd_295_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_fst_329_);
lean_dec(v_snd_295_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_box(0);
if (v_isShared_332_ == 0)
{
lean_ctor_set_tag(v___x_331_, 1);
lean_ctor_set(v___x_331_, 1, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_fst_329_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object* v_limit_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(v_limit_339_, v_a_340_);
lean_dec(v_limit_339_);
return v_res_341_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0));
v___x_344_ = lean_string_to_utf8(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_347_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_346_, v_a_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object* v_limits_351_, lean_object* v_a_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_array_354_; lean_object* v_idx_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_array_354_ = lean_ctor_get(v___y_353_, 0);
v_idx_355_ = lean_ctor_get(v___y_353_, 1);
v___x_356_ = lean_byte_array_size(v_array_354_);
v___x_357_ = lean_nat_dec_lt(v_idx_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___y_353_);
lean_ctor_set(v___x_358_, 1, v_a_352_);
return v___x_358_;
}
else
{
uint8_t v___x_359_; uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_byte_array_fget(v_array_354_, v_idx_355_);
v___x_360_ = 13;
v___x_361_ = lean_uint8_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___y_353_);
lean_ctor_set(v___x_362_, 1, v_a_352_);
return v___x_362_;
}
else
{
lean_object* v_maxLeadingEmptyLines_363_; uint8_t v___x_364_; 
v_maxLeadingEmptyLines_363_ = lean_ctor_get(v_limits_351_, 9);
v___x_364_ = lean_nat_dec_le(v_maxLeadingEmptyLines_363_, v_a_352_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_366_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_365_, v___y_353_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_pos_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_pos_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_pos_367_);
lean_dec_ref_known(v___x_366_, 2);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_add(v_a_352_, v___x_368_);
lean_dec(v_a_352_);
v_a_352_ = v___x_369_;
v___y_353_ = v_pos_367_;
goto _start;
}
else
{
lean_object* v_pos_371_; lean_object* v_err_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_a_352_);
v_pos_371_ = lean_ctor_get(v___x_366_, 0);
v_err_372_ = lean_ctor_get(v___x_366_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_366_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_err_372_);
lean_inc(v_pos_371_);
lean_dec(v___x_366_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_pos_371_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_err_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_a_352_);
v___x_380_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1));
v___x_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_381_, 0, v___y_353_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object* v_limits_382_, lean_object* v_a_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_382_, v_a_383_, v___y_384_);
lean_dec_ref(v_limits_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_count_388_; lean_object* v___x_389_; 
v_count_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_386_, v_count_388_, v_a_387_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_pos_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v_pos_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v___x_389_, 1);
lean_dec(v_unused_399_);
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_pos_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_box(0);
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
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_pos_390_);
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
lean_object* v_pos_400_; lean_object* v_err_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v_pos_400_ = lean_ctor_get(v___x_389_, 0);
v_err_401_ = lean_ctor_get(v___x_389_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_389_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_err_401_);
lean_inc(v_pos_400_);
lean_dec(v___x_389_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_pos_400_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_err_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object* v_limits_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_409_, v_a_410_);
lean_dec_ref(v_limits_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_412_, lean_object* v_inst_413_, lean_object* v_a_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_412_, v_a_414_, v___y_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_417_, lean_object* v_inst_418_, lean_object* v_a_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_417_, v_inst_418_, v_a_419_, v___y_420_);
lean_dec_ref(v_limits_417_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_425_){
_start:
{
lean_object* v_array_426_; lean_object* v_idx_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_array_426_ = lean_ctor_get(v_a_425_, 0);
v_idx_427_ = lean_ctor_get(v_a_425_, 1);
v___x_428_ = lean_byte_array_size(v_array_426_);
v___x_429_ = lean_nat_dec_lt(v_idx_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_431_, 0, v_a_425_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
return v___x_431_;
}
else
{
uint8_t v___x_432_; uint8_t v_got_433_; uint8_t v___x_434_; 
v___x_432_ = 32;
v_got_433_ = lean_byte_array_fget(v_array_426_, v_idx_427_);
v___x_434_ = lean_uint8_dec_eq(v_got_433_, v___x_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v_a_425_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
return v___x_436_;
}
else
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_447_; 
lean_inc(v_idx_427_);
lean_inc_ref(v_array_426_);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_425_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_448_ = lean_ctor_get(v_a_425_, 1);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_a_425_, 0);
lean_dec(v_unused_449_);
v___x_438_ = v_a_425_;
v_isShared_439_ = v_isSharedCheck_447_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_a_425_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_447_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_idx_427_, v___x_440_);
lean_dec(v_idx_427_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_array_426_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_446_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_box(0);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
return v___x_445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_pos_457_; lean_object* v_pos_461_; lean_object* v_maxSpaceSequence_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_snd_468_; lean_object* v_snd_469_; uint8_t v___x_470_; 
v_maxSpaceSequence_464_ = lean_ctor_get(v_limits_454_, 8);
v___x_465_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_465_, v_maxSpaceSequence_464_, v___x_466_, v_a_455_);
v_snd_468_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_snd_468_);
lean_dec_ref(v___x_467_);
v_snd_469_ = lean_ctor_get(v_snd_468_, 1);
v___x_470_ = lean_unbox(v_snd_469_);
if (v___x_470_ == 0)
{
lean_object* v_fst_471_; lean_object* v_array_472_; lean_object* v_idx_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_fst_471_ = lean_ctor_get(v_snd_468_, 0);
lean_inc(v_fst_471_);
lean_dec(v_snd_468_);
v_array_472_ = lean_ctor_get(v_fst_471_, 0);
v_idx_473_ = lean_ctor_get(v_fst_471_, 1);
v___x_474_ = lean_byte_array_size(v_array_472_);
v___x_475_ = lean_nat_dec_lt(v_idx_473_, v___x_474_);
if (v___x_475_ == 0)
{
v_pos_457_ = v_fst_471_;
goto v___jp_456_;
}
else
{
uint8_t v___x_476_; uint32_t v___x_477_; uint32_t v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_byte_array_fget(v_array_472_, v_idx_473_);
v___x_477_ = lean_uint8_to_uint32(v___x_476_);
v___x_478_ = 32;
v___x_479_ = lean_uint32_dec_eq(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = 9;
v___x_481_ = lean_uint32_dec_eq(v___x_477_, v___x_480_);
if (v___x_481_ == 0)
{
v_pos_457_ = v_fst_471_;
goto v___jp_456_;
}
else
{
v_pos_461_ = v_fst_471_;
goto v___jp_460_;
}
}
else
{
v_pos_461_ = v_fst_471_;
goto v___jp_460_;
}
}
}
else
{
lean_object* v_fst_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
v_fst_482_ = lean_ctor_get(v_snd_468_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_snd_468_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_snd_468_, 1);
lean_dec(v_unused_491_);
v___x_484_ = v_snd_468_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_fst_482_);
lean_dec(v_snd_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_box(0);
if (v_isShared_485_ == 0)
{
lean_ctor_set_tag(v___x_484_, 1);
lean_ctor_set(v___x_484_, 1, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_fst_482_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_box(0);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_pos_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
return v___x_459_;
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v_pos_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_492_, v_a_493_);
lean_dec_ref(v_limits_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_496_){
_start:
{
lean_object* v_array_497_; lean_object* v_idx_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_array_497_ = lean_ctor_get(v_a_496_, 0);
v_idx_498_ = lean_ctor_get(v_a_496_, 1);
v___x_499_ = lean_byte_array_size(v_array_497_);
v___x_500_ = lean_nat_dec_lt(v_idx_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_502_, 0, v_a_496_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_558_; 
lean_inc(v_idx_498_);
lean_inc_ref(v_array_497_);
v_isSharedCheck_558_ = !lean_is_exclusive(v_a_496_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; lean_object* v_unused_560_; 
v_unused_559_ = lean_ctor_get(v_a_496_, 1);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_a_496_, 0);
lean_dec(v_unused_560_);
v___x_504_ = v_a_496_;
v_isShared_505_ = v_isSharedCheck_558_;
goto v_resetjp_503_;
}
else
{
lean_dec(v_a_496_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_558_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v_c_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_it_x27_510_; 
v_c_506_ = lean_byte_array_fget(v_array_497_, v_idx_498_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_idx_498_, v___x_507_);
lean_dec(v_idx_498_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_508_);
v_it_x27_510_ = v___x_504_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_array_497_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_508_);
v_it_x27_510_ = v_reuseFailAlloc_557_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 48;
v___x_554_ = lean_uint8_dec_le(v___x_553_, v_c_506_);
if (v___x_554_ == 0)
{
goto v___jp_548_;
}
else
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = 57;
v___x_556_ = lean_uint8_dec_le(v_c_506_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_548_;
}
else
{
goto v___jp_528_;
}
}
v___jp_511_:
{
uint8_t v___x_512_; uint8_t v___x_513_; uint8_t v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_512_ = 97;
v___x_513_ = lean_uint8_sub(v_c_506_, v___x_512_);
v___x_514_ = 10;
v___x_515_ = lean_uint8_add(v___x_513_, v___x_514_);
v___x_516_ = lean_box(v___x_515_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_it_x27_510_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
return v___x_517_;
}
v___jp_518_:
{
uint8_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = 65;
v___x_520_ = lean_uint8_dec_le(v___x_519_, v_c_506_);
if (v___x_520_ == 0)
{
goto v___jp_511_;
}
else
{
uint8_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = 70;
v___x_522_ = lean_uint8_dec_le(v_c_506_, v___x_521_);
if (v___x_522_ == 0)
{
goto v___jp_511_;
}
else
{
uint8_t v___x_523_; uint8_t v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_523_ = lean_uint8_sub(v_c_506_, v___x_519_);
v___x_524_ = 10;
v___x_525_ = lean_uint8_add(v___x_523_, v___x_524_);
v___x_526_ = lean_box(v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_it_x27_510_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
return v___x_527_;
}
}
}
v___jp_528_:
{
uint8_t v___x_529_; uint8_t v___x_530_; 
v___x_529_ = 48;
v___x_530_ = lean_uint8_dec_le(v___x_529_, v_c_506_);
if (v___x_530_ == 0)
{
goto v___jp_518_;
}
else
{
uint8_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 57;
v___x_532_ = lean_uint8_dec_le(v_c_506_, v___x_531_);
if (v___x_532_ == 0)
{
goto v___jp_518_;
}
else
{
uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_uint8_sub(v_c_506_, v___x_529_);
v___x_534_ = lean_box(v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_it_x27_510_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
}
}
v___jp_536_:
{
lean_object* v___x_537_; uint32_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_537_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0));
v___x_538_ = lean_uint8_to_uint32(v_c_506_);
v___x_539_ = l_Char_quote(v___x_538_);
v___x_540_ = lean_string_append(v___x_537_, v___x_539_);
lean_dec_ref(v___x_539_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v_it_x27_510_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
v___jp_543_:
{
uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 65;
v___x_545_ = lean_uint8_dec_le(v___x_544_, v_c_506_);
if (v___x_545_ == 0)
{
goto v___jp_536_;
}
else
{
uint8_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = 70;
v___x_547_ = lean_uint8_dec_le(v_c_506_, v___x_546_);
if (v___x_547_ == 0)
{
goto v___jp_536_;
}
else
{
goto v___jp_528_;
}
}
}
v___jp_548_:
{
uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 97;
v___x_550_ = lean_uint8_dec_le(v___x_549_, v_c_506_);
if (v___x_550_ == 0)
{
goto v___jp_543_;
}
else
{
uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = 102;
v___x_552_ = lean_uint8_dec_le(v_c_506_, v___x_551_);
if (v___x_552_ == 0)
{
goto v___jp_543_;
}
else
{
goto v___jp_528_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object* v_acc_567_, lean_object* v_count_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
lean_inc_ref(v_a_569_);
v___x_570_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_pos_571_; lean_object* v_res_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_a_569_);
v_pos_571_ = lean_ctor_get(v___x_570_, 0);
v_res_572_ = lean_ctor_get(v___x_570_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_589_ == 0)
{
v___x_574_ = v___x_570_;
v_isShared_575_ = v_isSharedCheck_589_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_res_572_);
lean_inc(v_pos_571_);
lean_dec(v___x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_589_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_576_ = lean_unsigned_to_nat(16u);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_count_568_, v___x_577_);
lean_dec(v_count_568_);
v___x_579_ = lean_nat_dec_lt(v___x_576_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_del_object(v___x_574_);
v___x_580_ = lean_nat_mul(v_acc_567_, v___x_576_);
lean_dec(v_acc_567_);
v___x_581_ = lean_unbox(v_res_572_);
lean_dec(v_res_572_);
v___x_582_ = lean_uint8_to_nat(v___x_581_);
v___x_583_ = lean_nat_add(v___x_580_, v___x_582_);
lean_dec(v___x_580_);
v_acc_567_ = v___x_583_;
v_count_568_ = v___x_578_;
v_a_569_ = v_pos_571_;
goto _start;
}
else
{
lean_object* v___x_585_; lean_object* v___x_587_; 
lean_dec(v___x_578_);
lean_dec(v_res_572_);
lean_dec(v_acc_567_);
v___x_585_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 1, v___x_585_);
v___x_587_ = v___x_574_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_pos_571_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v_err_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_615_; 
v_err_590_ = lean_ctor_get(v___x_570_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_570_, 0);
lean_dec(v_unused_616_);
v___x_592_ = v___x_570_;
v_isShared_593_ = v_isSharedCheck_615_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_err_590_);
lean_dec(v___x_570_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_615_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_array_594_; lean_object* v_idx_595_; uint8_t v___x_596_; 
v_array_594_ = lean_ctor_get(v_a_569_, 0);
v_idx_595_ = lean_ctor_get(v_a_569_, 1);
v___x_596_ = lean_nat_dec_eq(v_idx_595_, v_idx_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v_count_568_);
lean_dec(v_acc_567_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v_a_569_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_err_590_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v___x_600_; uint8_t v___x_601_; 
lean_dec(v_err_590_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_dec_eq(v_count_568_, v___x_600_);
lean_dec(v_count_568_);
if (v___x_601_ == 0)
{
lean_object* v___x_603_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 0);
lean_ctor_set(v___x_592_, 1, v_acc_567_);
lean_ctor_set(v___x_592_, 0, v_a_569_);
v___x_603_ = v___x_592_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_acc_567_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; 
lean_dec(v_acc_567_);
v___x_605_ = lean_byte_array_size(v_array_594_);
v___x_606_ = lean_nat_dec_lt(v_idx_595_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = lean_box(0);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_607_);
lean_ctor_set(v___x_592_, 0, v_a_569_);
v___x_609_ = v___x_592_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_611_);
lean_ctor_set(v___x_592_, 0, v_a_569_);
v___x_613_ = v___x_592_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go_match__1_splitter___redArg(lean_object* v_____do__lift_617_, lean_object* v_h__1_618_, lean_object* v_h__2_619_){
_start:
{
if (lean_obj_tag(v_____do__lift_617_) == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_h__1_618_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_apply_1(v_h__2_619_, v___x_620_);
return v___x_621_;
}
else
{
lean_object* v_val_622_; lean_object* v___x_623_; 
lean_dec(v_h__2_619_);
v_val_622_ = lean_ctor_get(v_____do__lift_617_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v_____do__lift_617_, 1);
v___x_623_ = lean_apply_1(v_h__1_618_, v_val_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go_match__1_splitter(lean_object* v_motive_624_, lean_object* v_____do__lift_625_, lean_object* v_h__1_626_, lean_object* v_h__2_627_){
_start:
{
if (lean_obj_tag(v_____do__lift_625_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v_h__1_626_);
v___x_628_ = lean_box(0);
v___x_629_ = lean_apply_1(v_h__2_627_, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_val_630_; lean_object* v___x_631_; 
lean_dec(v_h__2_627_);
v_val_630_ = lean_ctor_get(v_____do__lift_625_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v_____do__lift_625_, 1);
v___x_631_ = lean_apply_1(v_h__1_626_, v_val_630_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_633_, v___x_633_, v_a_632_);
return v___x_634_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_637_ = lean_string_to_utf8(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_646_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_645_, v_a_644_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_pos_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_708_; 
v_pos_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v___x_646_, 1);
lean_dec(v_unused_709_);
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_708_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_pos_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_708_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_array_656_; lean_object* v_idx_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_array_656_ = lean_ctor_get(v_pos_647_, 0);
v_idx_657_ = lean_ctor_get(v_pos_647_, 1);
v___x_658_ = lean_byte_array_size(v_array_656_);
v___x_659_ = lean_nat_dec_lt(v_idx_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_del_object(v___x_649_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v_pos_647_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
return v___x_661_;
}
else
{
uint8_t v_c_662_; uint8_t v___x_663_; uint8_t v___x_664_; 
v_c_662_ = lean_byte_array_fget(v_array_656_, v_idx_657_);
v___x_663_ = 48;
v___x_664_ = lean_uint8_dec_le(v___x_663_, v_c_662_);
if (v___x_664_ == 0)
{
goto v___jp_651_;
}
else
{
uint8_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 57;
v___x_666_ = lean_uint8_dec_le(v_c_662_, v___x_665_);
if (v___x_666_ == 0)
{
goto v___jp_651_;
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_705_; 
lean_inc(v_idx_657_);
lean_inc_ref(v_array_656_);
lean_del_object(v___x_649_);
v_isSharedCheck_705_ = !lean_is_exclusive(v_pos_647_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; lean_object* v_unused_707_; 
v_unused_706_ = lean_ctor_get(v_pos_647_, 1);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_pos_647_, 0);
lean_dec(v_unused_707_);
v___x_668_ = v_pos_647_;
v_isShared_669_ = v_isSharedCheck_705_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_pos_647_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_705_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_it_x27_673_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_idx_657_, v___x_670_);
lean_dec(v_idx_657_);
lean_inc(v___x_671_);
lean_inc_ref(v_array_656_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_671_);
v_it_x27_673_ = v___x_668_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_array_656_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_671_);
v_it_x27_673_ = v_reuseFailAlloc_704_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
uint8_t v___x_674_; 
v___x_674_ = lean_nat_dec_lt(v___x_671_, v___x_658_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_671_);
lean_dec_ref(v_array_656_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_676_, 0, v_it_x27_673_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
return v___x_676_;
}
else
{
uint8_t v___x_677_; uint8_t v_got_678_; uint8_t v___x_679_; 
v___x_677_ = 46;
v_got_678_ = lean_byte_array_fget(v_array_656_, v___x_671_);
v___x_679_ = lean_uint8_dec_eq(v_got_678_, v___x_677_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec(v___x_671_);
lean_dec_ref(v_array_656_);
v___x_680_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5));
v___x_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_681_, 0, v_it_x27_673_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_687_; 
lean_dec_ref(v_it_x27_673_);
v___x_682_ = lean_nat_add(v___x_671_, v___x_670_);
lean_dec(v___x_671_);
lean_inc(v___x_682_);
lean_inc_ref(v_array_656_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_array_656_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_687_ = lean_nat_dec_lt(v___x_682_, v___x_658_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v___x_682_);
lean_dec_ref(v_array_656_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_683_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
return v___x_689_;
}
else
{
uint8_t v_c_690_; uint8_t v___x_691_; 
v_c_690_ = lean_byte_array_fget(v_array_656_, v___x_682_);
v___x_691_ = lean_uint8_dec_le(v___x_663_, v_c_690_);
if (v___x_691_ == 0)
{
lean_dec(v___x_682_);
lean_dec_ref(v_array_656_);
goto v___jp_684_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = lean_uint8_dec_le(v_c_690_, v___x_665_);
if (v___x_692_ == 0)
{
lean_dec(v___x_682_);
lean_dec_ref(v_array_656_);
goto v___jp_684_;
}
else
{
lean_object* v___x_693_; uint32_t v___x_694_; lean_object* v___x_695_; lean_object* v_it_x27_696_; uint32_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref_known(v___x_683_, 2);
v___x_693_ = lean_unsigned_to_nat(48u);
v___x_694_ = lean_uint8_to_uint32(v_c_662_);
v___x_695_ = lean_nat_add(v___x_682_, v___x_670_);
lean_dec(v___x_682_);
v_it_x27_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_696_, 0, v_array_656_);
lean_ctor_set(v_it_x27_696_, 1, v___x_695_);
v___x_697_ = lean_uint8_to_uint32(v_c_690_);
v___x_698_ = lean_uint32_to_nat(v___x_694_);
v___x_699_ = lean_nat_sub(v___x_698_, v___x_693_);
lean_dec(v___x_698_);
v___x_700_ = lean_uint32_to_nat(v___x_697_);
v___x_701_ = lean_nat_sub(v___x_700_, v___x_693_);
lean_dec(v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_699_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_it_x27_696_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
return v___x_703_;
}
}
}
v___jp_684_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_683_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
return v___x_686_;
}
}
}
}
}
}
}
}
v___jp_651_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 1);
lean_ctor_set(v___x_649_, 1, v___x_652_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_pos_647_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_pos_710_; lean_object* v_err_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
v_pos_710_ = lean_ctor_get(v___x_646_, 0);
v_err_711_ = lean_ctor_get(v___x_646_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_646_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_err_711_);
lean_inc(v_pos_710_);
lean_dec(v___x_646_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_pos_710_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_err_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_res_721_; lean_object* v_pos_722_; lean_object* v_fst_723_; lean_object* v_snd_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_res_721_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_res_721_);
v_pos_722_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_pos_722_);
lean_dec_ref_known(v___x_720_, 2);
v_fst_723_ = lean_ctor_get(v_res_721_, 0);
lean_inc(v_fst_723_);
v_snd_724_ = lean_ctor_get(v_res_721_, 1);
lean_inc(v_snd_724_);
lean_dec(v_res_721_);
v___x_725_ = l_Std_Http_Version_ofNumber_x3f(v_fst_723_, v_snd_724_);
lean_dec(v_snd_724_);
lean_dec(v_fst_723_);
v___x_726_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_725_, v_pos_722_);
lean_dec(v___x_725_);
return v___x_726_;
}
else
{
lean_object* v_pos_727_; lean_object* v_err_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_pos_727_ = lean_ctor_get(v___x_720_, 0);
v_err_728_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_720_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_err_728_);
lean_inc(v_pos_727_);
lean_dec(v___x_720_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_pos_727_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_err_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object* v_a_736_, lean_object* v_f_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_apply_1(v_a_736_, v___y_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_pos_740_; lean_object* v_res_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_pos_740_ = lean_ctor_get(v___x_739_, 0);
v_res_741_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_749_ == 0)
{
v___x_743_ = v___x_739_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_res_741_);
lean_inc(v_pos_740_);
lean_dec(v___x_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = lean_apply_1(v_f_737_, v_res_741_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_pos_740_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
lean_object* v_pos_750_; lean_object* v_err_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_f_737_);
v_pos_750_ = lean_ctor_get(v___x_739_, 0);
v_err_751_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_739_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_err_751_);
lean_inc(v_pos_750_);
lean_dec(v___x_739_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_pos_750_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_err_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_a_761_, lean_object* v_f_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v_a_761_, v_f_762_, v___y_763_);
return v___x_764_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object* v_x_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = 8;
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object* v_x_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_767_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object* v_x_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = 9;
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object* v_x_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_772_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object* v_x_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = 7;
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object* v_x_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_777_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object* v_x_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = 32;
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object* v_x_785_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = 0;
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object* v_x_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object* v_x_790_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = 28;
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object* v_x_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_792_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object* v_x_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = 31;
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object* v_x_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_797_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object* v_x_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = 1;
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object* v_x_802_){
_start:
{
uint8_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_802_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object* v_x_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = 2;
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object* v_x_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(v_x_807_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object* v_x_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = 5;
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_812_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object* v_x_815_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = 3;
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object* v_x_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_817_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object* v_x_820_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = 4;
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_822_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object* v_x_825_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = 6;
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object* v_x_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_827_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object* v_x_830_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = 10;
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_832_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object* v_x_835_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = 11;
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object* v_x_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object* v_x_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = 12;
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object* v_x_842_){
_start:
{
uint8_t v_res_843_; lean_object* v_r_844_; 
v_res_843_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_842_);
v_r_844_ = lean_box(v_res_843_);
return v_r_844_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object* v_x_845_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = 13;
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object* v_x_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_847_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object* v_x_850_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = 14;
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object* v_x_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object* v_x_855_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = 15;
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object* v_x_857_){
_start:
{
uint8_t v_res_858_; lean_object* v_r_859_; 
v_res_858_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_857_);
v_r_859_ = lean_box(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object* v_x_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = 16;
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object* v_x_862_){
_start:
{
uint8_t v_res_863_; lean_object* v_r_864_; 
v_res_863_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_862_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object* v_x_865_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = 17;
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object* v_x_867_){
_start:
{
uint8_t v_res_868_; lean_object* v_r_869_; 
v_res_868_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_867_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object* v_x_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = 18;
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_872_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object* v_x_875_){
_start:
{
uint8_t v___x_876_; 
v___x_876_ = 19;
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_877_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object* v_x_880_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = 20;
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object* v_x_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_882_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object* v_x_885_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = 21;
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_887_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object* v_x_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = 23;
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object* v_x_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_892_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object* v_x_895_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = 27;
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object* v_x_897_){
_start:
{
uint8_t v_res_898_; lean_object* v_r_899_; 
v_res_898_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_897_);
v_r_899_ = lean_box(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object* v_x_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = 22;
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object* v_x_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_902_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object* v_x_905_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = 24;
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object* v_x_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_907_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object* v_x_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = 25;
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object* v_x_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_912_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object* v_x_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = 26;
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object* v_x_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_917_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object* v_x_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = 29;
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object* v_x_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_922_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object* v_x_925_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = 30;
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object* v_x_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_927_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object* v_x_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = 33;
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object* v_x_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_932_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object* v_x_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = 34;
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object* v_x_937_){
_start:
{
uint8_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_937_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object* v_x_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = 35;
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object* v_x_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_942_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object* v_x_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = 36;
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object* v_x_947_){
_start:
{
uint8_t v_res_948_; lean_object* v_r_949_; 
v_res_948_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_947_);
v_r_949_ = lean_box(v_res_948_);
return v_r_949_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object* v_x_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = 38;
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object* v_x_952_){
_start:
{
uint8_t v_res_953_; lean_object* v_r_954_; 
v_res_953_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_952_);
v_r_954_ = lean_box(v_res_953_);
return v_r_954_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object* v_x_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = 37;
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object* v_x_957_){
_start:
{
uint8_t v_res_958_; lean_object* v_r_959_; 
v_res_958_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_957_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object* v_x_960_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = 39;
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object* v_x_962_){
_start:
{
uint8_t v_res_963_; lean_object* v_r_964_; 
v_res_963_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_962_);
v_r_964_ = lean_box(v_res_963_);
return v_r_964_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___x_968_ = lean_string_to_utf8(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2);
v___x_970_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5));
v___x_974_ = lean_string_to_utf8(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6);
v___x_976_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9));
v___x_980_ = lean_string_to_utf8(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10);
v___x_982_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13));
v___x_986_ = lean_string_to_utf8(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14);
v___x_988_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17));
v___x_992_ = lean_string_to_utf8(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18);
v___x_994_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21));
v___x_998_ = lean_string_to_utf8(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22);
v___x_1000_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25));
v___x_1004_ = lean_string_to_utf8(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26);
v___x_1006_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29));
v___x_1010_ = lean_string_to_utf8(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30);
v___x_1012_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33));
v___x_1016_ = lean_string_to_utf8(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34);
v___x_1018_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37));
v___x_1022_ = lean_string_to_utf8(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38);
v___x_1024_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41));
v___x_1028_ = lean_string_to_utf8(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42);
v___x_1030_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45));
v___x_1034_ = lean_string_to_utf8(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46);
v___x_1036_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49));
v___x_1040_ = lean_string_to_utf8(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50);
v___x_1042_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53));
v___x_1046_ = lean_string_to_utf8(v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54);
v___x_1048_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57));
v___x_1052_ = lean_string_to_utf8(v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58);
v___x_1054_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61));
v___x_1058_ = lean_string_to_utf8(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62);
v___x_1060_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65));
v___x_1064_ = lean_string_to_utf8(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66);
v___x_1066_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69));
v___x_1070_ = lean_string_to_utf8(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70);
v___x_1072_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73));
v___x_1076_ = lean_string_to_utf8(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74);
v___x_1078_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77));
v___x_1082_ = lean_string_to_utf8(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78);
v___x_1084_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81));
v___x_1088_ = lean_string_to_utf8(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82);
v___x_1090_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85));
v___x_1094_ = lean_string_to_utf8(v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86);
v___x_1096_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89));
v___x_1100_ = lean_string_to_utf8(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90);
v___x_1102_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93));
v___x_1106_ = lean_string_to_utf8(v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94);
v___x_1108_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97));
v___x_1112_ = lean_string_to_utf8(v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98);
v___x_1114_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101));
v___x_1118_ = lean_string_to_utf8(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102);
v___x_1120_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105));
v___x_1124_ = lean_string_to_utf8(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106);
v___x_1126_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109));
v___x_1130_ = lean_string_to_utf8(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110);
v___x_1132_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113));
v___x_1136_ = lean_string_to_utf8(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114);
v___x_1138_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117));
v___x_1142_ = lean_string_to_utf8(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118);
v___x_1144_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121));
v___x_1148_ = lean_string_to_utf8(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122);
v___x_1150_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125));
v___x_1154_ = lean_string_to_utf8(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126);
v___x_1156_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129));
v___x_1160_ = lean_string_to_utf8(v___x_1159_);
return v___x_1160_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130);
v___x_1162_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133));
v___x_1166_ = lean_string_to_utf8(v___x_1165_);
return v___x_1166_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134);
v___x_1168_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137));
v___x_1172_ = lean_string_to_utf8(v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138);
v___x_1174_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141));
v___x_1178_ = lean_string_to_utf8(v___x_1177_);
return v___x_1178_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142);
v___x_1180_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145));
v___x_1184_ = lean_string_to_utf8(v___x_1183_);
return v___x_1184_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146);
v___x_1186_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149));
v___x_1190_ = lean_string_to_utf8(v___x_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150);
v___x_1192_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153));
v___x_1196_ = lean_string_to_utf8(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154);
v___x_1198_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157));
v___x_1202_ = lean_string_to_utf8(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158);
v___x_1204_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_1208_){
_start:
{
lean_object* v___f_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___f_1209_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0));
v___x_1210_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3);
lean_inc_ref(v_a_1208_);
v___x_1211_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1210_, v___f_1209_, v_a_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1211_;
}
else
{
lean_object* v_err_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1367_; 
v_err_1212_ = lean_ctor_get(v___x_1211_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1211_, 0);
lean_dec(v_unused_1368_);
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1367_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_err_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1367_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_idx_1216_; uint8_t v___x_1217_; 
v_idx_1216_ = lean_ctor_get(v_a_1208_, 1);
v___x_1217_ = lean_nat_dec_eq(v_idx_1216_, v_idx_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1219_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_a_1208_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1208_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_err_1212_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
else
{
lean_object* v___f_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_del_object(v___x_1214_);
lean_dec(v_err_1212_);
v___f_1221_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4));
v___x_1222_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7);
lean_inc_ref(v_a_1208_);
v___x_1223_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1222_, v___f_1221_, v_a_1208_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1223_;
}
else
{
lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref_known(v___x_1223_, 2);
v___f_1224_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8));
v___x_1225_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11);
lean_inc_ref(v_a_1208_);
v___x_1226_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1225_, v___f_1224_, v_a_1208_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1226_;
}
else
{
lean_object* v___f_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref_known(v___x_1226_, 2);
v___f_1227_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12));
v___x_1228_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15);
lean_inc_ref(v_a_1208_);
v___x_1229_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1228_, v___f_1227_, v_a_1208_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1229_;
}
else
{
lean_object* v___f_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec_ref_known(v___x_1229_, 2);
v___f_1230_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16));
v___x_1231_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19);
lean_inc_ref(v_a_1208_);
v___x_1232_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1231_, v___f_1230_, v_a_1208_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1232_;
}
else
{
lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec_ref_known(v___x_1232_, 2);
v___f_1233_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__20));
v___x_1234_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23);
lean_inc_ref(v_a_1208_);
v___x_1235_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1234_, v___f_1233_, v_a_1208_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1235_;
}
else
{
lean_object* v___f_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec_ref_known(v___x_1235_, 2);
v___f_1236_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24));
v___x_1237_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27);
lean_inc_ref(v_a_1208_);
v___x_1238_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1237_, v___f_1236_, v_a_1208_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1238_;
}
else
{
lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1238_, 2);
v___f_1239_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28));
v___x_1240_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31);
lean_inc_ref(v_a_1208_);
v___x_1241_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1240_, v___f_1239_, v_a_1208_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1241_;
}
else
{
lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref_known(v___x_1241_, 2);
v___f_1242_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32));
v___x_1243_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35);
lean_inc_ref(v_a_1208_);
v___x_1244_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1243_, v___f_1242_, v_a_1208_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1244_;
}
else
{
lean_object* v___f_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref_known(v___x_1244_, 2);
v___f_1245_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36));
v___x_1246_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39);
lean_inc_ref(v_a_1208_);
v___x_1247_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1246_, v___f_1245_, v_a_1208_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1247_;
}
else
{
lean_object* v___f_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref_known(v___x_1247_, 2);
v___f_1248_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40));
v___x_1249_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43);
lean_inc_ref(v_a_1208_);
v___x_1250_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1249_, v___f_1248_, v_a_1208_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1250_;
}
else
{
lean_object* v___f_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref_known(v___x_1250_, 2);
v___f_1251_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44));
v___x_1252_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47);
lean_inc_ref(v_a_1208_);
v___x_1253_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1252_, v___f_1251_, v_a_1208_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1253_;
}
else
{
lean_object* v___f_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec_ref_known(v___x_1253_, 2);
v___f_1254_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48));
v___x_1255_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51);
lean_inc_ref(v_a_1208_);
v___x_1256_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1255_, v___f_1254_, v_a_1208_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1256_;
}
else
{
lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec_ref_known(v___x_1256_, 2);
v___f_1257_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52));
v___x_1258_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55);
lean_inc_ref(v_a_1208_);
v___x_1259_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1258_, v___f_1257_, v_a_1208_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1259_;
}
else
{
lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec_ref_known(v___x_1259_, 2);
v___f_1260_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56));
v___x_1261_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59);
lean_inc_ref(v_a_1208_);
v___x_1262_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1261_, v___f_1260_, v_a_1208_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1262_;
}
else
{
lean_object* v___f_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec_ref_known(v___x_1262_, 2);
v___f_1263_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60));
v___x_1264_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63);
lean_inc_ref(v_a_1208_);
v___x_1265_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1264_, v___f_1263_, v_a_1208_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1265_;
}
else
{
lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec_ref_known(v___x_1265_, 2);
v___f_1266_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64));
v___x_1267_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67);
lean_inc_ref(v_a_1208_);
v___x_1268_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1267_, v___f_1266_, v_a_1208_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1268_;
}
else
{
lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref_known(v___x_1268_, 2);
v___f_1269_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68));
v___x_1270_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71);
lean_inc_ref(v_a_1208_);
v___x_1271_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1270_, v___f_1269_, v_a_1208_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1271_;
}
else
{
lean_object* v___f_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec_ref_known(v___x_1271_, 2);
v___f_1272_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72));
v___x_1273_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75);
lean_inc_ref(v_a_1208_);
v___x_1274_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1273_, v___f_1272_, v_a_1208_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1274_;
}
else
{
lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec_ref_known(v___x_1274_, 2);
v___f_1275_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76));
v___x_1276_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79);
lean_inc_ref(v_a_1208_);
v___x_1277_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1276_, v___f_1275_, v_a_1208_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1277_;
}
else
{
lean_object* v___f_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref_known(v___x_1277_, 2);
v___f_1278_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80));
v___x_1279_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83);
lean_inc_ref(v_a_1208_);
v___x_1280_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1279_, v___f_1278_, v_a_1208_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1280_;
}
else
{
lean_object* v___f_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec_ref_known(v___x_1280_, 2);
v___f_1281_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84));
v___x_1282_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87);
lean_inc_ref(v_a_1208_);
v___x_1283_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1282_, v___f_1281_, v_a_1208_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1283_;
}
else
{
lean_object* v___f_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec_ref_known(v___x_1283_, 2);
v___f_1284_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88));
v___x_1285_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91);
lean_inc_ref(v_a_1208_);
v___x_1286_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1285_, v___f_1284_, v_a_1208_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1286_;
}
else
{
lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref_known(v___x_1286_, 2);
v___f_1287_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92));
v___x_1288_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95);
lean_inc_ref(v_a_1208_);
v___x_1289_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1288_, v___f_1287_, v_a_1208_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1289_;
}
else
{
lean_object* v___f_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref_known(v___x_1289_, 2);
v___f_1290_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96));
v___x_1291_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99);
lean_inc_ref(v_a_1208_);
v___x_1292_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1291_, v___f_1290_, v_a_1208_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1292_;
}
else
{
lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec_ref_known(v___x_1292_, 2);
v___f_1293_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100));
v___x_1294_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103);
lean_inc_ref(v_a_1208_);
v___x_1295_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1294_, v___f_1293_, v_a_1208_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1295_;
}
else
{
lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec_ref_known(v___x_1295_, 2);
v___f_1296_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104));
v___x_1297_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107);
lean_inc_ref(v_a_1208_);
v___x_1298_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1297_, v___f_1296_, v_a_1208_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1298_;
}
else
{
lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref_known(v___x_1298_, 2);
v___f_1299_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108));
v___x_1300_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111);
lean_inc_ref(v_a_1208_);
v___x_1301_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1300_, v___f_1299_, v_a_1208_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1301_;
}
else
{
lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec_ref_known(v___x_1301_, 2);
v___f_1302_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112));
v___x_1303_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115);
lean_inc_ref(v_a_1208_);
v___x_1304_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1303_, v___f_1302_, v_a_1208_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1304_;
}
else
{
lean_object* v___f_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec_ref_known(v___x_1304_, 2);
v___f_1305_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116));
v___x_1306_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119);
lean_inc_ref(v_a_1208_);
v___x_1307_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1306_, v___f_1305_, v_a_1208_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1307_;
}
else
{
lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref_known(v___x_1307_, 2);
v___f_1308_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120));
v___x_1309_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123);
lean_inc_ref(v_a_1208_);
v___x_1310_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1309_, v___f_1308_, v_a_1208_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1310_;
}
else
{
lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref_known(v___x_1310_, 2);
v___f_1311_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124));
v___x_1312_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127);
lean_inc_ref(v_a_1208_);
v___x_1313_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1312_, v___f_1311_, v_a_1208_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1313_;
}
else
{
lean_object* v___f_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref_known(v___x_1313_, 2);
v___f_1314_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128));
v___x_1315_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131);
lean_inc_ref(v_a_1208_);
v___x_1316_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1315_, v___f_1314_, v_a_1208_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1316_;
}
else
{
lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref_known(v___x_1316_, 2);
v___f_1317_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132));
v___x_1318_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135);
lean_inc_ref(v_a_1208_);
v___x_1319_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1318_, v___f_1317_, v_a_1208_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1319_;
}
else
{
lean_object* v___f_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref_known(v___x_1319_, 2);
v___f_1320_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136));
v___x_1321_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139);
lean_inc_ref(v_a_1208_);
v___x_1322_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1321_, v___f_1320_, v_a_1208_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1322_;
}
else
{
lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref_known(v___x_1322_, 2);
v___f_1323_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140));
v___x_1324_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143);
lean_inc_ref(v_a_1208_);
v___x_1325_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1324_, v___f_1323_, v_a_1208_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1325_;
}
else
{
lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec_ref_known(v___x_1325_, 2);
v___f_1326_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144));
v___x_1327_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147);
lean_inc_ref(v_a_1208_);
v___x_1328_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1327_, v___f_1326_, v_a_1208_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1328_;
}
else
{
lean_object* v___f_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref_known(v___x_1328_, 2);
v___f_1329_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148));
v___x_1330_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151);
lean_inc_ref(v_a_1208_);
v___x_1331_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1330_, v___f_1329_, v_a_1208_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1331_;
}
else
{
lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref_known(v___x_1331_, 2);
v___f_1332_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152));
v___x_1333_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155);
lean_inc_ref(v_a_1208_);
v___x_1334_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1333_, v___f_1332_, v_a_1208_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1334_;
}
else
{
lean_object* v___f_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref_known(v___x_1334_, 2);
v___f_1335_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156));
v___x_1336_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159);
lean_inc_ref(v_a_1208_);
v___x_1337_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1336_, v___f_1335_, v_a_1208_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_dec_ref(v_a_1208_);
return v___x_1337_;
}
else
{
lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1364_; 
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; lean_object* v_unused_1366_; 
v_unused_1365_ = lean_ctor_get(v___x_1337_, 1);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v___x_1337_, 0);
lean_dec(v_unused_1366_);
v___x_1339_ = v___x_1337_;
v_isShared_1340_ = v_isSharedCheck_1364_;
goto v_resetjp_1338_;
}
else
{
lean_dec(v___x_1337_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1364_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_snd_1345_; lean_object* v_snd_1346_; uint8_t v___x_1347_; 
v___f_1341_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1342_ = lean_unsigned_to_nat(64u);
v___x_1343_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1208_);
v___x_1344_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1341_, v___x_1342_, v___x_1343_, v_a_1208_);
v_snd_1345_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_snd_1345_);
v_snd_1346_ = lean_ctor_get(v_snd_1345_, 1);
v___x_1347_ = lean_unbox(v_snd_1346_);
if (v___x_1347_ == 0)
{
lean_object* v_fst_1348_; lean_object* v_fst_1349_; uint8_t v___x_1350_; 
v_fst_1348_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_fst_1348_);
lean_dec_ref(v___x_1344_);
v_fst_1349_ = lean_ctor_get(v_snd_1345_, 0);
lean_inc(v_fst_1349_);
lean_dec(v_snd_1345_);
v___x_1350_ = lean_nat_dec_eq(v_fst_1348_, v___x_1343_);
lean_dec(v_fst_1348_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec_ref(v_a_1208_);
v___x_1351_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161));
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1351_);
lean_ctor_set(v___x_1339_, 0, v_fst_1349_);
v___x_1353_ = v___x_1339_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_fst_1349_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_dec(v_fst_1349_);
v___x_1355_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1355_);
lean_ctor_set(v___x_1339_, 0, v_a_1208_);
v___x_1357_ = v___x_1339_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1208_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_fst_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
lean_dec_ref(v___x_1344_);
lean_dec_ref(v_a_1208_);
v_fst_1359_ = lean_ctor_get(v_snd_1345_, 0);
lean_inc(v_fst_1359_);
lean_dec(v_snd_1345_);
v___x_1360_ = lean_box(0);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v___x_1360_);
lean_ctor_set(v___x_1339_, 0, v_fst_1359_);
v___x_1362_ = v___x_1339_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_fst_1359_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1369_){
_start:
{
uint8_t v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = 32;
v___x_1371_ = lean_uint8_dec_eq(v_b_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
uint8_t v___x_1372_; 
v___x_1372_ = 1;
return v___x_1372_;
}
else
{
uint8_t v___x_1373_; 
v___x_1373_ = 0;
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1374_){
_start:
{
uint8_t v_b_boxed_1375_; uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_b_boxed_1375_ = lean_unbox(v_b_1374_);
v_res_1376_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1375_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v_maxUriLength_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_snd_1393_; lean_object* v_snd_1394_; uint8_t v___x_1395_; 
v_maxUriLength_1389_ = lean_ctor_get(v_limits_1382_, 4);
v___f_1390_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_1391_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1383_);
v___x_1392_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1390_, v_maxUriLength_1389_, v___x_1391_, v_a_1383_);
v_snd_1393_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_snd_1393_);
v_snd_1394_ = lean_ctor_get(v_snd_1393_, 1);
v___x_1395_ = lean_unbox(v_snd_1394_);
if (v___x_1395_ == 0)
{
lean_object* v_fst_1396_; lean_object* v_fst_1397_; lean_object* v_array_1398_; lean_object* v_idx_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1426_; 
v_fst_1396_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_fst_1396_);
lean_dec_ref(v___x_1392_);
v_fst_1397_ = lean_ctor_get(v_snd_1393_, 0);
lean_inc(v_fst_1397_);
lean_dec(v_snd_1393_);
v_array_1398_ = lean_ctor_get(v_a_1383_, 0);
v_idx_1399_ = lean_ctor_get(v_a_1383_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_a_1383_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1401_ = v_a_1383_;
v_isShared_1402_ = v_isSharedCheck_1426_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_idx_1399_);
lean_inc(v_array_1398_);
lean_dec(v_a_1383_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1426_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_lower_1404_; lean_object* v_upper_1405_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___y_1423_; uint8_t v___x_1425_; 
v___x_1420_ = lean_nat_add(v_idx_1399_, v_fst_1396_);
lean_dec(v_fst_1396_);
v___x_1421_ = lean_byte_array_size(v_array_1398_);
v___x_1425_ = lean_nat_dec_le(v_idx_1399_, v___x_1391_);
if (v___x_1425_ == 0)
{
v___y_1423_ = v_idx_1399_;
goto v___jp_1422_;
}
else
{
lean_dec(v_idx_1399_);
v___y_1423_ = v___x_1391_;
goto v___jp_1422_;
}
v___jp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1406_ = l_ByteArray_toByteSlice(v_array_1398_, v_lower_1404_, v_upper_1405_);
v___x_1407_ = l_ByteSlice_size(v___x_1406_);
v___x_1408_ = lean_nat_dec_eq(v___x_1407_, v_maxUriLength_1389_);
lean_dec(v___x_1407_);
if (v___x_1408_ == 0)
{
lean_del_object(v___x_1401_);
v___y_1385_ = v___x_1406_;
v___y_1386_ = v_fst_1397_;
goto v___jp_1384_;
}
else
{
lean_object* v_array_1409_; lean_object* v_idx_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_array_1409_ = lean_ctor_get(v_fst_1397_, 0);
v_idx_1410_ = lean_ctor_get(v_fst_1397_, 1);
v___x_1411_ = lean_byte_array_size(v_array_1409_);
v___x_1412_ = lean_nat_dec_lt(v_idx_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_del_object(v___x_1401_);
v___y_1385_ = v___x_1406_;
v___y_1386_ = v_fst_1397_;
goto v___jp_1384_;
}
else
{
uint8_t v___x_1413_; uint8_t v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = lean_byte_array_fget(v_array_1409_, v_idx_1410_);
v___x_1414_ = 32;
v___x_1415_ = lean_uint8_dec_eq(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_dec_ref(v___x_1406_);
v___x_1416_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 1);
lean_ctor_set(v___x_1401_, 1, v___x_1416_);
lean_ctor_set(v___x_1401_, 0, v_fst_1397_);
v___x_1418_ = v___x_1401_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_fst_1397_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
else
{
lean_del_object(v___x_1401_);
v___y_1385_ = v___x_1406_;
v___y_1386_ = v_fst_1397_;
goto v___jp_1384_;
}
}
}
}
v___jp_1422_:
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_le(v___x_1420_, v___x_1421_);
if (v___x_1424_ == 0)
{
lean_dec(v___x_1420_);
v_lower_1404_ = v___y_1423_;
v_upper_1405_ = v___x_1421_;
goto v___jp_1403_;
}
else
{
v_lower_1404_ = v___y_1423_;
v_upper_1405_ = v___x_1420_;
goto v___jp_1403_;
}
}
}
}
else
{
lean_object* v_fst_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v___x_1392_);
lean_dec_ref(v_a_1383_);
v_fst_1427_ = lean_ctor_get(v_snd_1393_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_snd_1393_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_snd_1393_, 1);
lean_dec(v_unused_1436_);
v___x_1429_ = v_snd_1393_;
v_isShared_1430_ = v_isSharedCheck_1435_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_fst_1427_);
lean_dec(v_snd_1393_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1435_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = lean_box(0);
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 1);
lean_ctor_set(v___x_1429_, 1, v___x_1431_);
v___x_1433_ = v___x_1429_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_fst_1427_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
v___jp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = l_ByteSlice_toByteArray(v___y_1385_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___y_1386_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1437_, v_a_1438_);
lean_dec_ref(v_limits_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_pos_1446_; lean_object* v_array_1447_; lean_object* v_idx_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_pos_1446_ = lean_ctor_get(v___x_1445_, 0);
v_array_1447_ = lean_ctor_get(v_pos_1446_, 0);
v_idx_1448_ = lean_ctor_get(v_pos_1446_, 1);
v___x_1449_ = lean_byte_array_size(v_array_1447_);
v___x_1450_ = lean_nat_dec_lt(v_idx_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
return v___x_1445_;
}
else
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
lean_inc(v_pos_1446_);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1459_ = lean_ctor_get(v___x_1445_, 1);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1460_);
v___x_1452_ = v___x_1445_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v___x_1445_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
lean_ctor_set(v___x_1452_, 1, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_pos_1446_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_pos_1474_; lean_object* v_res_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1552_; 
v_pos_1474_ = lean_ctor_get(v___x_1473_, 0);
v_res_1475_ = lean_ctor_get(v___x_1473_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1477_ = v___x_1473_;
v_isShared_1478_ = v_isSharedCheck_1552_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_res_1475_);
lean_inc(v_pos_1474_);
lean_dec(v___x_1473_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1552_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_array_1479_; lean_object* v_idx_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v_array_1479_ = lean_ctor_get(v_pos_1474_, 0);
v_idx_1480_ = lean_ctor_get(v_pos_1474_, 1);
v___x_1481_ = lean_byte_array_size(v_array_1479_);
v___x_1482_ = lean_nat_dec_lt(v_idx_1480_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
lean_dec(v_res_1475_);
v___x_1483_ = lean_box(0);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 1);
lean_ctor_set(v___x_1477_, 1, v___x_1483_);
v___x_1485_ = v___x_1477_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_pos_1474_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
else
{
uint8_t v___x_1487_; uint8_t v_got_1488_; uint8_t v___x_1489_; 
v___x_1487_ = 32;
v_got_1488_ = lean_byte_array_fget(v_array_1479_, v_idx_1480_);
v___x_1489_ = lean_uint8_dec_eq(v_got_1488_, v___x_1487_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_dec(v_res_1475_);
v___x_1490_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 1);
lean_ctor_set(v___x_1477_, 1, v___x_1490_);
v___x_1492_ = v___x_1477_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_pos_1474_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1549_; 
lean_inc(v_idx_1480_);
lean_inc_ref(v_array_1479_);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_pos_1474_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; lean_object* v_unused_1551_; 
v_unused_1550_ = lean_ctor_get(v_pos_1474_, 1);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_pos_1474_, 0);
lean_dec(v_unused_1551_);
v___x_1495_ = v_pos_1474_;
v_isShared_1496_ = v_isSharedCheck_1549_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v_pos_1474_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1549_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = lean_unsigned_to_nat(1u);
v___x_1498_ = lean_nat_add(v_idx_1480_, v___x_1497_);
lean_dec(v_idx_1480_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_array_1479_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___f_1501_; lean_object* v___x_1502_; 
v___f_1501_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_1502_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1501_, v_res_1475_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1513_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1513_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1513_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set_tag(v___x_1505_, 1);
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1510_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 1);
lean_ctor_set(v___x_1477_, 1, v___x_1508_);
lean_ctor_set(v___x_1477_, 0, v___x_1500_);
v___x_1510_ = v___x_1477_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1508_);
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
else
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1477_);
v_a_1514_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1502_, 1);
v___x_1515_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v___x_1500_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_pos_1516_; lean_object* v_res_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_pos_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_pos_1516_);
v_res_1517_ = lean_ctor_get(v___x_1515_, 1);
lean_inc(v_res_1517_);
lean_dec_ref_known(v___x_1515_, 2);
v___x_1518_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_1519_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1518_, v_pos_1516_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_pos_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1528_; 
v_pos_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v___x_1519_, 1);
lean_dec(v_unused_1529_);
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_pos_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_a_1514_);
lean_ctor_set(v___x_1524_, 1, v_res_1517_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_pos_1520_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
else
{
lean_object* v_pos_1530_; lean_object* v_err_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_res_1517_);
lean_dec(v_a_1514_);
v_pos_1530_ = lean_ctor_get(v___x_1519_, 0);
v_err_1531_ = lean_ctor_get(v___x_1519_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1519_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_err_1531_);
lean_inc(v_pos_1530_);
lean_dec(v___x_1519_);
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
else
{
lean_object* v_pos_1539_; lean_object* v_err_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v_a_1514_);
v_pos_1539_ = lean_ctor_get(v___x_1515_, 0);
v_err_1540_ = lean_ctor_get(v___x_1515_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1515_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_err_1540_);
lean_inc(v_pos_1539_);
lean_dec(v___x_1515_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_pos_1539_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_err_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
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
lean_object* v_pos_1553_; lean_object* v_err_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_pos_1553_ = lean_ctor_get(v___x_1473_, 0);
v_err_1554_ = lean_ctor_get(v___x_1473_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1473_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_err_1554_);
lean_inc(v_pos_1553_);
lean_dec(v___x_1473_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_pos_1553_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_err_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1562_, v_a_1563_);
lean_dec_ref(v_limits_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1568_, v_a_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_pos_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1661_; 
v_pos_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v___x_1570_, 1);
lean_dec(v_unused_1662_);
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1661_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_pos_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1661_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1571_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_pos_1576_; lean_object* v_res_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1651_; 
v_pos_1576_ = lean_ctor_get(v___x_1575_, 0);
v_res_1577_ = lean_ctor_get(v___x_1575_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1579_ = v___x_1575_;
v_isShared_1580_ = v_isSharedCheck_1651_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_res_1577_);
lean_inc(v_pos_1576_);
lean_dec(v___x_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1651_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_array_1581_; lean_object* v_idx_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_array_1581_ = lean_ctor_get(v_pos_1576_, 0);
v_idx_1582_ = lean_ctor_get(v_pos_1576_, 1);
v___x_1583_ = lean_byte_array_size(v_array_1581_);
v___x_1584_ = lean_nat_dec_lt(v_idx_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
lean_dec(v_res_1577_);
lean_del_object(v___x_1573_);
v___x_1585_ = lean_box(0);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
lean_ctor_set(v___x_1579_, 1, v___x_1585_);
v___x_1587_ = v___x_1579_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_pos_1576_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
else
{
uint8_t v___x_1589_; uint8_t v_got_1590_; uint8_t v___x_1591_; 
v___x_1589_ = 32;
v_got_1590_ = lean_byte_array_fget(v_array_1581_, v_idx_1582_);
v___x_1591_ = lean_uint8_dec_eq(v_got_1590_, v___x_1589_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_dec(v_res_1577_);
lean_del_object(v___x_1573_);
v___x_1592_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
lean_ctor_set(v___x_1579_, 1, v___x_1592_);
v___x_1594_ = v___x_1579_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_pos_1576_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
else
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1648_; 
lean_inc(v_idx_1582_);
lean_inc_ref(v_array_1581_);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_pos_1576_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; 
v_unused_1649_ = lean_ctor_get(v_pos_1576_, 1);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_pos_1576_, 0);
lean_dec(v_unused_1650_);
v___x_1597_ = v_pos_1576_;
v_isShared_1598_ = v_isSharedCheck_1648_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v_pos_1576_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1648_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1599_ = lean_unsigned_to_nat(1u);
v___x_1600_ = lean_nat_add(v_idx_1582_, v___x_1599_);
lean_dec(v_idx_1582_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 1, v___x_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_array_1581_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; 
v___x_1603_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1568_, v___x_1602_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_pos_1604_; lean_object* v_res_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1637_; 
v_pos_1604_ = lean_ctor_get(v___x_1603_, 0);
v_res_1605_ = lean_ctor_get(v___x_1603_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1607_ = v___x_1603_;
v_isShared_1608_ = v_isSharedCheck_1637_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_res_1605_);
lean_inc(v_pos_1604_);
lean_dec(v___x_1603_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1637_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_snd_1614_; lean_object* v_fst_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; uint8_t v___x_1618_; 
v_snd_1614_ = lean_ctor_get(v_res_1605_, 1);
lean_inc(v_snd_1614_);
v_fst_1615_ = lean_ctor_get(v_res_1605_, 0);
lean_inc(v_fst_1615_);
lean_dec(v_res_1605_);
v_fst_1616_ = lean_ctor_get(v_snd_1614_, 0);
lean_inc(v_fst_1616_);
v_snd_1617_ = lean_ctor_get(v_snd_1614_, 1);
lean_inc(v_snd_1617_);
lean_dec(v_snd_1614_);
v___x_1618_ = lean_nat_dec_eq(v_fst_1616_, v___x_1599_);
lean_dec(v_fst_1616_);
if (v___x_1618_ == 0)
{
lean_del_object(v___x_1573_);
goto v___jp_1619_;
}
else
{
uint8_t v___x_1629_; 
v___x_1629_ = lean_nat_dec_eq(v_snd_1617_, v___x_1599_);
if (v___x_1629_ == 0)
{
lean_del_object(v___x_1573_);
goto v___jp_1619_;
}
else
{
uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1635_; 
lean_dec(v_snd_1617_);
lean_del_object(v___x_1607_);
lean_del_object(v___x_1579_);
v___x_1630_ = 1;
v___x_1631_ = l_Std_Http_Headers_empty;
v___x_1632_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1632_, 0, v_fst_1615_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_unbox(v_res_1577_);
lean_dec(v_res_1577_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*2, v___x_1633_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*2 + 1, v___x_1630_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1632_);
lean_ctor_set(v___x_1573_, 0, v_pos_1604_);
v___x_1635_ = v___x_1573_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_pos_1604_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v___x_1632_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
v___jp_1609_:
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 1);
lean_ctor_set(v___x_1607_, 1, v___x_1610_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_pos_1604_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
v___jp_1619_:
{
if (v___x_1618_ == 0)
{
lean_dec(v_snd_1617_);
lean_dec(v_fst_1615_);
lean_del_object(v___x_1579_);
lean_dec(v_res_1577_);
goto v___jp_1609_;
}
else
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_nat_dec_eq(v_snd_1617_, v___x_1620_);
lean_dec(v_snd_1617_);
if (v___x_1621_ == 0)
{
lean_dec(v_fst_1615_);
lean_del_object(v___x_1579_);
lean_dec(v_res_1577_);
goto v___jp_1609_;
}
else
{
uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1627_; 
lean_del_object(v___x_1607_);
v___x_1622_ = 0;
v___x_1623_ = l_Std_Http_Headers_empty;
v___x_1624_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1624_, 0, v_fst_1615_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_unbox(v_res_1577_);
lean_dec(v_res_1577_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*2, v___x_1625_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*2 + 1, v___x_1622_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v___x_1624_);
lean_ctor_set(v___x_1579_, 0, v_pos_1604_);
v___x_1627_ = v___x_1579_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_pos_1604_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1624_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1638_; lean_object* v_err_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_del_object(v___x_1579_);
lean_dec(v_res_1577_);
lean_del_object(v___x_1573_);
v_pos_1638_ = lean_ctor_get(v___x_1603_, 0);
v_err_1639_ = lean_ctor_get(v___x_1603_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1603_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_err_1639_);
lean_inc(v_pos_1638_);
lean_dec(v___x_1603_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_pos_1638_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_err_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
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
lean_object* v_pos_1652_; lean_object* v_err_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_del_object(v___x_1573_);
v_pos_1652_ = lean_ctor_get(v___x_1575_, 0);
v_err_1653_ = lean_ctor_get(v___x_1575_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1575_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_err_1653_);
lean_inc(v_pos_1652_);
lean_dec(v___x_1575_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_pos_1652_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_err_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
else
{
lean_object* v_pos_1663_; lean_object* v_err_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_pos_1663_ = lean_ctor_get(v___x_1570_, 0);
v_err_1664_ = lean_ctor_get(v___x_1570_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1570_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_err_1664_);
lean_inc(v_pos_1663_);
lean_dec(v___x_1570_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_pos_1663_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_err_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_1672_, v_a_1673_);
lean_dec_ref(v_limits_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_1675_, v_a_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_pos_1678_; lean_object* v___x_1679_; 
v_pos_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_pos_1678_);
lean_dec_ref_known(v___x_1677_, 2);
v___x_1679_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_pos_1680_; lean_object* v_res_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1751_; 
v_pos_1680_ = lean_ctor_get(v___x_1679_, 0);
v_res_1681_ = lean_ctor_get(v___x_1679_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1683_ = v___x_1679_;
v_isShared_1684_ = v_isSharedCheck_1751_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_res_1681_);
lean_inc(v_pos_1680_);
lean_dec(v___x_1679_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1751_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v_array_1685_; lean_object* v_idx_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_array_1685_ = lean_ctor_get(v_pos_1680_, 0);
v_idx_1686_ = lean_ctor_get(v_pos_1680_, 1);
v___x_1687_ = lean_byte_array_size(v_array_1685_);
v___x_1688_ = lean_nat_dec_lt(v_idx_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_dec(v_res_1681_);
v___x_1689_ = lean_box(0);
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 1);
lean_ctor_set(v___x_1683_, 1, v___x_1689_);
v___x_1691_ = v___x_1683_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_pos_1680_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
uint8_t v___x_1693_; uint8_t v_got_1694_; uint8_t v___x_1695_; 
v___x_1693_ = 32;
v_got_1694_ = lean_byte_array_fget(v_array_1685_, v_idx_1686_);
v___x_1695_ = lean_uint8_dec_eq(v_got_1694_, v___x_1693_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
lean_dec(v_res_1681_);
v___x_1696_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 1);
lean_ctor_set(v___x_1683_, 1, v___x_1696_);
v___x_1698_ = v___x_1683_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_pos_1680_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
else
{
lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1748_; 
lean_inc(v_idx_1686_);
lean_inc_ref(v_array_1685_);
lean_del_object(v___x_1683_);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_pos_1680_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; lean_object* v_unused_1750_; 
v_unused_1749_ = lean_ctor_get(v_pos_1680_, 1);
lean_dec(v_unused_1749_);
v_unused_1750_ = lean_ctor_get(v_pos_1680_, 0);
lean_dec(v_unused_1750_);
v___x_1701_ = v_pos_1680_;
v_isShared_1702_ = v_isSharedCheck_1748_;
goto v_resetjp_1700_;
}
else
{
lean_dec(v_pos_1680_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1748_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_add(v_idx_1686_, v___x_1703_);
lean_dec(v_idx_1686_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_array_1685_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_1675_, v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_res_1708_; lean_object* v_snd_1709_; lean_object* v_pos_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1736_; 
v_res_1708_ = lean_ctor_get(v___x_1707_, 1);
lean_inc(v_res_1708_);
v_snd_1709_ = lean_ctor_get(v_res_1708_, 1);
lean_inc(v_snd_1709_);
v_pos_1710_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1707_, 1);
lean_dec(v_unused_1737_);
v___x_1712_ = v___x_1707_;
v_isShared_1713_ = v_isSharedCheck_1736_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_pos_1710_);
lean_dec(v___x_1707_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1736_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_fst_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1734_; 
v_fst_1714_ = lean_ctor_get(v_res_1708_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_res_1708_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_res_1708_, 1);
lean_dec(v_unused_1735_);
v___x_1716_ = v_res_1708_;
v_isShared_1717_ = v_isSharedCheck_1734_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_fst_1714_);
lean_dec(v_res_1708_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1734_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v_fst_1718_; lean_object* v_snd_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1733_; 
v_fst_1718_ = lean_ctor_get(v_snd_1709_, 0);
v_snd_1719_ = lean_ctor_get(v_snd_1709_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_snd_1709_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1721_ = v_snd_1709_;
v_isShared_1722_ = v_isSharedCheck_1733_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_snd_1719_);
lean_inc(v_fst_1718_);
lean_dec(v_snd_1709_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1733_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1723_ = l_Std_Http_Version_ofNumber_x3f(v_fst_1718_, v_snd_1719_);
lean_dec(v_snd_1719_);
lean_dec(v_fst_1718_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v___x_1723_);
lean_ctor_set(v___x_1721_, 0, v_fst_1714_);
v___x_1725_ = v___x_1721_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_fst_1714_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1727_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v___x_1725_);
lean_ctor_set(v___x_1716_, 0, v_res_1681_);
v___x_1727_ = v___x_1716_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_res_1681_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___x_1727_);
v___x_1729_ = v___x_1712_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_pos_1710_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_1738_; lean_object* v_err_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_res_1681_);
v_pos_1738_ = lean_ctor_get(v___x_1707_, 0);
v_err_1739_ = lean_ctor_get(v___x_1707_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1707_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_err_1739_);
lean_inc(v_pos_1738_);
lean_dec(v___x_1707_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_pos_1738_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_err_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
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
lean_object* v_pos_1752_; lean_object* v_err_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
v_pos_1752_ = lean_ctor_get(v___x_1679_, 0);
v_err_1753_ = lean_ctor_get(v___x_1679_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1679_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_err_1753_);
lean_inc(v_pos_1752_);
lean_dec(v___x_1679_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_pos_1752_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_err_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_pos_1761_; lean_object* v_err_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_pos_1761_ = lean_ctor_get(v___x_1677_, 0);
v_err_1762_ = lean_ctor_get(v___x_1677_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1677_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_err_1762_);
lean_inc(v_pos_1761_);
lean_dec(v___x_1677_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_pos_1761_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_err_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_1770_, v_a_1771_);
lean_dec_ref(v_limits_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_1773_){
_start:
{
uint32_t v___x_1774_; uint32_t v___x_1782_; uint8_t v___x_1783_; 
v___x_1774_ = lean_uint8_to_uint32(v___y_1773_);
v___x_1782_ = 33;
v___x_1783_ = lean_uint32_dec_le(v___x_1782_, v___x_1774_);
if (v___x_1783_ == 0)
{
goto v___jp_1775_;
}
else
{
uint32_t v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = 126;
v___x_1785_ = lean_uint32_dec_le(v___x_1774_, v___x_1784_);
if (v___x_1785_ == 0)
{
goto v___jp_1775_;
}
else
{
return v___x_1785_;
}
}
v___jp_1775_:
{
uint32_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = 128;
v___x_1777_ = lean_uint32_dec_le(v___x_1776_, v___x_1774_);
if (v___x_1777_ == 0)
{
uint32_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = 32;
v___x_1779_ = lean_uint32_dec_eq(v___x_1774_, v___x_1778_);
if (v___x_1779_ == 0)
{
uint32_t v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = 9;
v___x_1781_ = lean_uint32_dec_eq(v___x_1774_, v___x_1780_);
return v___x_1781_;
}
else
{
return v___x_1779_;
}
}
else
{
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_1786_){
_start:
{
uint8_t v___y_3635__boxed_1787_; uint8_t v_res_1788_; lean_object* v_r_1789_; 
v___y_3635__boxed_1787_ = lean_unbox(v___y_1786_);
v_res_1788_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_3635__boxed_1787_);
v_r_1789_ = lean_box(v_res_1788_);
return v_r_1789_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(uint8_t v___y_1790_){
_start:
{
uint32_t v___x_1791_; uint32_t v___x_1792_; uint8_t v___x_1793_; 
v___x_1791_ = lean_uint8_to_uint32(v___y_1790_);
v___x_1792_ = 32;
v___x_1793_ = lean_uint32_dec_eq(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
uint32_t v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = 9;
v___x_1795_ = lean_uint32_dec_eq(v___x_1791_, v___x_1794_);
return v___x_1795_;
}
else
{
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0___boxed(lean_object* v___y_1796_){
_start:
{
uint8_t v___y_3662__boxed_1797_; uint8_t v_res_1798_; lean_object* v_r_1799_; 
v___y_3662__boxed_1797_ = lean_unbox(v___y_1796_);
v_res_1798_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__0(v___y_3662__boxed_1797_);
v_r_1799_ = lean_box(v_res_1798_);
return v_r_1799_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_1800_, lean_object* v_pos_1801_){
_start:
{
lean_object* v_str_1802_; lean_object* v_startInclusive_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v_decide_1807_; 
v_str_1802_ = lean_ctor_get(v_s_1800_, 0);
v_startInclusive_1803_ = lean_ctor_get(v_s_1800_, 1);
v___x_1804_ = lean_nat_add(v_startInclusive_1803_, v_pos_1801_);
v___x_1805_ = lean_nat_sub(v___x_1804_, v_startInclusive_1803_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v_decide_1807_ = lean_nat_dec_eq(v___x_1805_, v___x_1806_);
if (v_decide_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1816_; uint32_t v___x_1817_; uint32_t v___x_1818_; uint8_t v___x_1819_; 
lean_inc(v_startInclusive_1803_);
lean_inc_ref(v_str_1802_);
v___x_1808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1808_, 0, v_str_1802_);
lean_ctor_set(v___x_1808_, 1, v_startInclusive_1803_);
lean_ctor_set(v___x_1808_, 2, v___x_1804_);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_nat_sub(v___x_1805_, v___x_1809_);
lean_dec(v___x_1805_);
v___x_1811_ = l_String_Slice_posLE(v___x_1808_, v___x_1810_);
lean_dec_ref_known(v___x_1808_, 3);
v___x_1816_ = lean_nat_add(v_startInclusive_1803_, v___x_1811_);
v___x_1817_ = lean_string_utf8_get_fast(v_str_1802_, v___x_1816_);
lean_dec(v___x_1816_);
v___x_1818_ = 32;
v___x_1819_ = lean_uint32_dec_eq(v___x_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
uint32_t v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = 9;
v___x_1821_ = lean_uint32_dec_eq(v___x_1817_, v___x_1820_);
if (v___x_1821_ == 0)
{
uint32_t v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = 13;
v___x_1823_ = lean_uint32_dec_eq(v___x_1817_, v___x_1822_);
if (v___x_1823_ == 0)
{
uint32_t v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = 10;
v___x_1825_ = lean_uint32_dec_eq(v___x_1817_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec(v___x_1811_);
return v_pos_1801_;
}
else
{
goto v___jp_1812_;
}
}
else
{
goto v___jp_1812_;
}
}
else
{
goto v___jp_1812_;
}
}
else
{
goto v___jp_1812_;
}
v___jp_1812_:
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = lean_nat_add(v___x_1811_, v___x_1809_);
v___x_1814_ = lean_nat_dec_le(v___x_1813_, v_pos_1801_);
lean_dec(v___x_1813_);
if (v___x_1814_ == 0)
{
lean_dec(v___x_1811_);
return v_pos_1801_;
}
else
{
lean_dec(v_pos_1801_);
v_pos_1801_ = v___x_1811_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1805_);
lean_dec(v___x_1804_);
return v_pos_1801_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_1826_, lean_object* v_pos_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_1826_, v_pos_1827_);
lean_dec_ref(v_s_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_pos_1838_; lean_object* v_pos_1842_; lean_object* v_maxHeaderNameLength_1845_; lean_object* v_maxHeaderValueLength_1846_; lean_object* v_maxSpaceSequence_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1885_; lean_object* v_pos_1886_; lean_object* v_res_1887_; lean_object* v___x_1893_; lean_object* v_snd_1894_; lean_object* v_snd_1895_; uint8_t v___x_1896_; 
v_maxHeaderNameLength_1845_ = lean_ctor_get(v_limits_1835_, 6);
v_maxHeaderValueLength_1846_ = lean_ctor_get(v_limits_1835_, 7);
v_maxSpaceSequence_1847_ = lean_ctor_get(v_limits_1835_, 8);
v___f_1848_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_1849_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1836_);
v___x_1893_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1848_, v_maxHeaderNameLength_1845_, v___x_1849_, v_a_1836_);
v_snd_1894_ = lean_ctor_get(v___x_1893_, 1);
lean_inc(v_snd_1894_);
v_snd_1895_ = lean_ctor_get(v_snd_1894_, 1);
v___x_1896_ = lean_unbox(v_snd_1895_);
if (v___x_1896_ == 0)
{
lean_object* v_fst_1897_; lean_object* v_fst_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_2056_; 
v_fst_1897_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_fst_1897_);
lean_dec_ref(v___x_1893_);
v_fst_1898_ = lean_ctor_get(v_snd_1894_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_snd_1894_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_snd_1894_, 1);
lean_dec(v_unused_2057_);
v___x_1900_ = v_snd_1894_;
v_isShared_1901_ = v_isSharedCheck_2056_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_fst_1898_);
lean_dec(v_snd_1894_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_2056_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
uint8_t v___x_1902_; 
v___x_1902_ = lean_nat_dec_eq(v_fst_1897_, v___x_1849_);
if (v___x_1902_ == 0)
{
lean_object* v_array_1903_; lean_object* v_idx_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_2051_; 
v_array_1903_ = lean_ctor_get(v_a_1836_, 0);
v_idx_1904_ = lean_ctor_get(v_a_1836_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_1836_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_1906_ = v_a_1836_;
v_isShared_1907_ = v_isSharedCheck_2051_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_idx_1904_);
lean_inc(v_array_1903_);
lean_dec(v_a_1836_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_2051_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___f_1908_; lean_object* v___f_1909_; lean_object* v___y_1911_; lean_object* v_pos_1912_; lean_object* v_res_1913_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v_lower_1943_; lean_object* v_upper_1944_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1956_; lean_object* v_pos_1957_; lean_object* v___y_1984_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___y_2042_; uint8_t v___x_2050_; 
v___f_1908_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___f_1909_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_2039_ = lean_nat_add(v_idx_1904_, v_fst_1897_);
lean_dec(v_fst_1897_);
v___x_2040_ = lean_byte_array_size(v_array_1903_);
v___x_2050_ = lean_nat_dec_le(v_idx_1904_, v___x_1849_);
if (v___x_2050_ == 0)
{
v___y_2042_ = v_idx_1904_;
goto v___jp_2041_;
}
else
{
lean_dec(v_idx_1904_);
v___y_2042_ = v___x_1849_;
goto v___jp_2041_;
}
v___jp_1910_:
{
lean_object* v___x_1914_; lean_object* v_snd_1915_; lean_object* v_snd_1916_; uint8_t v___x_1917_; 
v___x_1914_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1909_, v_maxSpaceSequence_1847_, v___x_1849_, v_pos_1912_);
v_snd_1915_ = lean_ctor_get(v___x_1914_, 1);
lean_inc(v_snd_1915_);
lean_dec_ref(v___x_1914_);
v_snd_1916_ = lean_ctor_get(v_snd_1915_, 1);
v___x_1917_ = lean_unbox(v_snd_1916_);
if (v___x_1917_ == 0)
{
lean_object* v_fst_1918_; lean_object* v_array_1919_; lean_object* v_idx_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_fst_1918_ = lean_ctor_get(v_snd_1915_, 0);
lean_inc(v_fst_1918_);
lean_dec(v_snd_1915_);
v_array_1919_ = lean_ctor_get(v_fst_1918_, 0);
v_idx_1920_ = lean_ctor_get(v_fst_1918_, 1);
v___x_1921_ = lean_byte_array_size(v_array_1919_);
v___x_1922_ = lean_nat_dec_lt(v_idx_1920_, v___x_1921_);
if (v___x_1922_ == 0)
{
v___y_1885_ = v___y_1911_;
v_pos_1886_ = v_fst_1918_;
v_res_1887_ = v_res_1913_;
goto v___jp_1884_;
}
else
{
uint8_t v___x_1923_; uint32_t v___x_1924_; uint32_t v___x_1925_; uint8_t v___x_1926_; 
v___x_1923_ = lean_byte_array_fget(v_array_1919_, v_idx_1920_);
v___x_1924_ = lean_uint8_to_uint32(v___x_1923_);
v___x_1925_ = 32;
v___x_1926_ = lean_uint32_dec_eq(v___x_1924_, v___x_1925_);
if (v___x_1926_ == 0)
{
uint32_t v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = 9;
v___x_1928_ = lean_uint32_dec_eq(v___x_1924_, v___x_1927_);
if (v___x_1928_ == 0)
{
v___y_1885_ = v___y_1911_;
v_pos_1886_ = v_fst_1918_;
v_res_1887_ = v_res_1913_;
goto v___jp_1884_;
}
else
{
lean_dec(v_res_1913_);
lean_dec_ref(v___y_1911_);
v_pos_1838_ = v_fst_1918_;
goto v___jp_1837_;
}
}
else
{
lean_dec(v_res_1913_);
lean_dec_ref(v___y_1911_);
v_pos_1838_ = v_fst_1918_;
goto v___jp_1837_;
}
}
}
else
{
lean_object* v_fst_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_res_1913_);
lean_dec_ref(v___y_1911_);
v_fst_1929_ = lean_ctor_get(v_snd_1915_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_snd_1915_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_snd_1915_, 1);
lean_dec(v_unused_1938_);
v___x_1931_ = v_snd_1915_;
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_fst_1929_);
lean_dec(v_snd_1915_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = lean_box(0);
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 1, v___x_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_fst_1929_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
v___jp_1939_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = l_ByteArray_toByteSlice(v___y_1941_, v_lower_1943_, v_upper_1944_);
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
v___y_1911_ = v___y_1940_;
v_pos_1912_ = v___y_1942_;
v_res_1913_ = v___x_1946_;
goto v___jp_1910_;
}
v___jp_1947_:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_nat_dec_le(v___y_1952_, v___y_1950_);
if (v___x_1954_ == 0)
{
lean_dec(v___y_1952_);
v___y_1940_ = v___y_1948_;
v___y_1941_ = v___y_1949_;
v___y_1942_ = v___y_1951_;
v_lower_1943_ = v___y_1953_;
v_upper_1944_ = v___y_1950_;
goto v___jp_1939_;
}
else
{
lean_dec(v___y_1950_);
v___y_1940_ = v___y_1948_;
v___y_1941_ = v___y_1949_;
v___y_1942_ = v___y_1951_;
v_lower_1943_ = v___y_1953_;
v_upper_1944_ = v___y_1952_;
goto v___jp_1939_;
}
}
v___jp_1955_:
{
lean_object* v___x_1958_; lean_object* v_snd_1959_; lean_object* v_snd_1960_; uint8_t v___x_1961_; 
lean_inc_ref(v_pos_1957_);
v___x_1958_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1908_, v_maxHeaderValueLength_1846_, v___x_1849_, v_pos_1957_);
v_snd_1959_ = lean_ctor_get(v___x_1958_, 1);
lean_inc(v_snd_1959_);
v_snd_1960_ = lean_ctor_get(v_snd_1959_, 1);
v___x_1961_ = lean_unbox(v_snd_1960_);
if (v___x_1961_ == 0)
{
lean_object* v_fst_1962_; lean_object* v_fst_1963_; lean_object* v_array_1964_; lean_object* v_idx_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_fst_1962_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_fst_1962_);
lean_dec_ref(v___x_1958_);
v_fst_1963_ = lean_ctor_get(v_snd_1959_, 0);
lean_inc(v_fst_1963_);
lean_dec(v_snd_1959_);
v_array_1964_ = lean_ctor_get(v_pos_1957_, 0);
lean_inc_ref(v_array_1964_);
v_idx_1965_ = lean_ctor_get(v_pos_1957_, 1);
lean_inc(v_idx_1965_);
lean_dec_ref(v_pos_1957_);
v___x_1966_ = lean_nat_add(v_idx_1965_, v_fst_1962_);
lean_dec(v_fst_1962_);
v___x_1967_ = lean_byte_array_size(v_array_1964_);
v___x_1968_ = lean_nat_dec_le(v_idx_1965_, v___x_1849_);
if (v___x_1968_ == 0)
{
v___y_1948_ = v___y_1956_;
v___y_1949_ = v_array_1964_;
v___y_1950_ = v___x_1967_;
v___y_1951_ = v_fst_1963_;
v___y_1952_ = v___x_1966_;
v___y_1953_ = v_idx_1965_;
goto v___jp_1947_;
}
else
{
lean_dec(v_idx_1965_);
v___y_1948_ = v___y_1956_;
v___y_1949_ = v_array_1964_;
v___y_1950_ = v___x_1967_;
v___y_1951_ = v_fst_1963_;
v___y_1952_ = v___x_1966_;
v___y_1953_ = v___x_1849_;
goto v___jp_1947_;
}
}
else
{
lean_object* v_fst_1969_; lean_object* v_idx_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v___x_1958_);
v_fst_1969_ = lean_ctor_get(v_snd_1959_, 0);
lean_inc(v_fst_1969_);
lean_dec(v_snd_1959_);
v_idx_1970_ = lean_ctor_get(v_pos_1957_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_pos_1957_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v_pos_1957_, 0);
lean_dec(v_unused_1982_);
v___x_1972_ = v_pos_1957_;
v_isShared_1973_ = v_isSharedCheck_1981_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_idx_1970_);
lean_dec(v_pos_1957_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1981_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_idx_1974_; uint8_t v___x_1975_; 
v_idx_1974_ = lean_ctor_get(v_fst_1969_, 1);
v___x_1975_ = lean_nat_dec_eq(v_idx_1970_, v_idx_1974_);
lean_dec(v_idx_1970_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_dec_ref(v___y_1956_);
v___x_1976_ = lean_box(0);
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 1);
lean_ctor_set(v___x_1972_, 1, v___x_1976_);
lean_ctor_set(v___x_1972_, 0, v_fst_1969_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_fst_1969_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
else
{
lean_object* v___x_1980_; 
lean_del_object(v___x_1972_);
v___x_1980_ = lean_box(0);
v___y_1911_ = v___y_1956_;
v_pos_1912_ = v_fst_1969_;
v_res_1913_ = v___x_1980_;
goto v___jp_1910_;
}
}
}
}
v___jp_1983_:
{
lean_object* v_array_1985_; lean_object* v_idx_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v_array_1985_ = lean_ctor_get(v_fst_1898_, 0);
v_idx_1986_ = lean_ctor_get(v_fst_1898_, 1);
v___x_1987_ = lean_byte_array_size(v_array_1985_);
v___x_1988_ = lean_nat_dec_lt(v_idx_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_array_1903_);
v___x_1989_ = lean_box(0);
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 1);
lean_ctor_set(v___x_1906_, 1, v___x_1989_);
lean_ctor_set(v___x_1906_, 0, v_fst_1898_);
v___x_1991_ = v___x_1906_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_fst_1898_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
else
{
uint8_t v___x_1993_; uint8_t v_got_1994_; uint8_t v___x_1995_; 
v___x_1993_ = 58;
v_got_1994_ = lean_byte_array_fget(v_array_1985_, v_idx_1986_);
v___x_1995_ = lean_uint8_dec_eq(v_got_1994_, v___x_1993_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_array_1903_);
v___x_1996_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__4));
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 1);
lean_ctor_set(v___x_1906_, 1, v___x_1996_);
lean_ctor_set(v___x_1906_, 0, v_fst_1898_);
v___x_1998_ = v___x_1906_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_fst_1898_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
else
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2036_; 
lean_inc(v_idx_1986_);
lean_inc_ref(v_array_1985_);
lean_del_object(v___x_1906_);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_fst_1898_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; lean_object* v_unused_2038_; 
v_unused_2037_ = lean_ctor_get(v_fst_1898_, 1);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_fst_1898_, 0);
lean_dec(v_unused_2038_);
v___x_2001_ = v_fst_1898_;
v_isShared_2002_ = v_isSharedCheck_2036_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v_fst_1898_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2036_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_add(v_idx_1986_, v___x_2003_);
lean_dec(v_idx_1986_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___x_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_array_1985_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v_snd_2008_; lean_object* v_snd_2009_; uint8_t v___x_2010_; 
v___x_2007_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1909_, v_maxSpaceSequence_1847_, v___x_1849_, v___x_2006_);
v_snd_2008_ = lean_ctor_get(v___x_2007_, 1);
lean_inc(v_snd_2008_);
lean_dec_ref(v___x_2007_);
v_snd_2009_ = lean_ctor_get(v_snd_2008_, 1);
v___x_2010_ = lean_unbox(v_snd_2009_);
if (v___x_2010_ == 0)
{
lean_object* v_fst_2011_; lean_object* v_array_2012_; lean_object* v_idx_2013_; lean_object* v_lower_2014_; lean_object* v_upper_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_fst_2011_ = lean_ctor_get(v_snd_2008_, 0);
lean_inc(v_fst_2011_);
lean_dec(v_snd_2008_);
v_array_2012_ = lean_ctor_get(v_fst_2011_, 0);
v_idx_2013_ = lean_ctor_get(v_fst_2011_, 1);
v_lower_2014_ = lean_ctor_get(v___y_1984_, 0);
lean_inc(v_lower_2014_);
v_upper_2015_ = lean_ctor_get(v___y_1984_, 1);
lean_inc(v_upper_2015_);
lean_dec_ref(v___y_1984_);
v___x_2016_ = l_ByteArray_toByteSlice(v_array_1903_, v_lower_2014_, v_upper_2015_);
v___x_2017_ = lean_byte_array_size(v_array_2012_);
v___x_2018_ = lean_nat_dec_lt(v_idx_2013_, v___x_2017_);
if (v___x_2018_ == 0)
{
v___y_1956_ = v___x_2016_;
v_pos_1957_ = v_fst_2011_;
goto v___jp_1955_;
}
else
{
uint8_t v___x_2019_; uint32_t v___x_2020_; uint32_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2019_ = lean_byte_array_fget(v_array_2012_, v_idx_2013_);
v___x_2020_ = lean_uint8_to_uint32(v___x_2019_);
v___x_2021_ = 32;
v___x_2022_ = lean_uint32_dec_eq(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
uint32_t v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = 9;
v___x_2024_ = lean_uint32_dec_eq(v___x_2020_, v___x_2023_);
if (v___x_2024_ == 0)
{
v___y_1956_ = v___x_2016_;
v_pos_1957_ = v_fst_2011_;
goto v___jp_1955_;
}
else
{
lean_dec_ref(v___x_2016_);
v_pos_1842_ = v_fst_2011_;
goto v___jp_1841_;
}
}
else
{
lean_dec_ref(v___x_2016_);
v_pos_1842_ = v_fst_2011_;
goto v___jp_1841_;
}
}
}
else
{
lean_object* v_fst_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_array_1903_);
v_fst_2025_ = lean_ctor_get(v_snd_2008_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_snd_2008_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v_snd_2008_, 1);
lean_dec(v_unused_2034_);
v___x_2027_ = v_snd_2008_;
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_fst_2025_);
lean_dec(v_snd_2008_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_box(0);
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 1);
lean_ctor_set(v___x_2027_, 1, v___x_2029_);
v___x_2031_ = v___x_2027_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_fst_2025_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
}
}
}
v___jp_2041_:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_nat_dec_le(v___x_2039_, v___x_2040_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2045_; 
lean_dec(v___x_2039_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___x_2040_);
lean_ctor_set(v___x_1900_, 0, v___y_2042_);
v___x_2045_ = v___x_1900_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___y_2042_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v___x_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
v___y_1984_ = v___x_2045_;
goto v___jp_1983_;
}
}
else
{
lean_object* v___x_2048_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___x_2039_);
lean_ctor_set(v___x_1900_, 0, v___y_2042_);
v___x_2048_ = v___x_1900_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___y_2042_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2039_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
v___y_1984_ = v___x_2048_;
goto v___jp_1983_;
}
}
}
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
lean_dec(v_fst_1898_);
lean_dec(v_fst_1897_);
v___x_2052_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 1);
lean_ctor_set(v___x_1900_, 1, v___x_2052_);
lean_ctor_set(v___x_1900_, 0, v_a_1836_);
v___x_2054_ = v___x_1900_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_1836_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_fst_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v___x_1893_);
lean_dec_ref(v_a_1836_);
v_fst_2058_ = lean_ctor_get(v_snd_1894_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_snd_1894_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; 
v_unused_2067_ = lean_ctor_get(v_snd_1894_, 1);
lean_dec(v_unused_2067_);
v___x_2060_ = v_snd_1894_;
v_isShared_2061_ = v_isSharedCheck_2066_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_fst_2058_);
lean_dec(v_snd_1894_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2066_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = lean_box(0);
if (v_isShared_2061_ == 0)
{
lean_ctor_set_tag(v___x_2060_, 1);
lean_ctor_set(v___x_2060_, 1, v___x_2062_);
v___x_2064_ = v___x_2060_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_fst_2058_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
v___jp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_pos_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
return v___x_1840_;
}
v___jp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_pos_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
return v___x_1844_;
}
v___jp_1850_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1854_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_1855_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___y_1853_, v___x_1849_, v___x_1854_);
lean_dec_ref(v___y_1853_);
v___x_1856_ = lean_string_utf8_byte_size(v___x_1855_);
lean_inc_ref(v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1849_);
lean_ctor_set(v___x_1857_, 2, v___x_1856_);
v___x_1858_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_1857_, v___x_1856_);
lean_dec_ref_known(v___x_1857_, 3);
v___x_1859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1855_);
lean_ctor_set(v___x_1859_, 1, v___x_1849_);
lean_ctor_set(v___x_1859_, 2, v___x_1858_);
v___x_1860_ = l_String_Slice_toString(v___x_1859_);
lean_dec_ref_known(v___x_1859_, 3);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___y_1852_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___y_1851_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
return v___x_1862_;
}
v___jp_1863_:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_1866_, v___y_1865_);
lean_dec(v___y_1866_);
if (lean_obj_tag(v___x_1867_) == 0)
{
if (lean_obj_tag(v___y_1864_) == 0)
{
lean_object* v_pos_1868_; lean_object* v_res_1869_; lean_object* v___x_1870_; 
v_pos_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_pos_1868_);
v_res_1869_ = lean_ctor_get(v___x_1867_, 1);
lean_inc(v_res_1869_);
lean_dec_ref_known(v___x_1867_, 2);
v___x_1870_ = l_ByteArray_empty;
v___y_1851_ = v_pos_1868_;
v___y_1852_ = v_res_1869_;
v___y_1853_ = v___x_1870_;
goto v___jp_1850_;
}
else
{
lean_object* v_pos_1871_; lean_object* v_res_1872_; lean_object* v_val_1873_; lean_object* v___x_1874_; 
v_pos_1871_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_pos_1871_);
v_res_1872_ = lean_ctor_get(v___x_1867_, 1);
lean_inc(v_res_1872_);
lean_dec_ref_known(v___x_1867_, 2);
v_val_1873_ = lean_ctor_get(v___y_1864_, 0);
lean_inc(v_val_1873_);
lean_dec_ref_known(v___y_1864_, 1);
v___x_1874_ = l_ByteSlice_toByteArray(v_val_1873_);
v___y_1851_ = v_pos_1871_;
v___y_1852_ = v_res_1872_;
v___y_1853_ = v___x_1874_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_pos_1875_; lean_object* v_err_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v___y_1864_);
v_pos_1875_ = lean_ctor_get(v___x_1867_, 0);
v_err_1876_ = lean_ctor_get(v___x_1867_, 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1867_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_err_1876_);
lean_inc(v_pos_1875_);
lean_dec(v___x_1867_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_pos_1875_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_err_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
v___jp_1884_:
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = l_ByteSlice_toByteArray(v___y_1885_);
v___x_1889_ = lean_string_validate_utf8(v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; 
lean_dec_ref(v___x_1888_);
v___x_1890_ = lean_box(0);
v___y_1864_ = v_res_1887_;
v___y_1865_ = v_pos_1886_;
v___y_1866_ = v___x_1890_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_string_from_utf8_unchecked(v___x_1888_);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
v___y_1864_ = v_res_1887_;
v___y_1865_ = v_pos_1886_;
v___y_1866_ = v___x_1892_;
goto v___jp_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2068_, v_a_2069_);
lean_dec_ref(v_limits_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2071_, lean_object* v_x_2072_){
_start:
{
if (lean_obj_tag(v_x_2071_) == 0)
{
if (lean_obj_tag(v_x_2072_) == 0)
{
uint8_t v___x_2073_; 
v___x_2073_ = 1;
return v___x_2073_;
}
else
{
uint8_t v___x_2074_; 
v___x_2074_ = 0;
return v___x_2074_;
}
}
else
{
if (lean_obj_tag(v_x_2072_) == 0)
{
uint8_t v___x_2075_; 
v___x_2075_ = 0;
return v___x_2075_;
}
else
{
lean_object* v_val_2076_; lean_object* v_val_2077_; uint8_t v___x_2078_; uint8_t v___x_2079_; uint8_t v___x_2080_; 
v_val_2076_ = lean_ctor_get(v_x_2071_, 0);
v_val_2077_ = lean_ctor_get(v_x_2072_, 0);
v___x_2078_ = lean_unbox(v_val_2076_);
v___x_2079_ = lean_unbox(v_val_2077_);
v___x_2080_ = lean_uint8_dec_eq(v___x_2078_, v___x_2079_);
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2081_, v_x_2082_);
lean_dec(v_x_2082_);
lean_dec(v_x_2081_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v___y_2094_; lean_object* v_pos_2117_; lean_object* v_res_2118_; lean_object* v_array_2156_; lean_object* v_idx_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v_array_2156_ = lean_ctor_get(v_a_2092_, 0);
v_idx_2157_ = lean_ctor_get(v_a_2092_, 1);
v___x_2158_ = lean_byte_array_size(v_array_2156_);
v___x_2159_ = lean_nat_dec_lt(v_idx_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_box(0);
v_pos_2117_ = v_a_2092_;
v_res_2118_ = v___x_2160_;
goto v___jp_2116_;
}
else
{
uint8_t v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_byte_array_fget(v_array_2156_, v_idx_2157_);
v___x_2162_ = lean_box(v___x_2161_);
v___x_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
v_pos_2117_ = v_a_2092_;
v_res_2118_ = v___x_2163_;
goto v___jp_2116_;
}
v___jp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2096_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2095_, v___y_2094_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_pos_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2105_; 
v_pos_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v___x_2096_, 1);
lean_dec(v_unused_2106_);
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_pos_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2101_ = lean_box(0);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2101_);
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_pos_2097_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
else
{
lean_object* v_pos_2107_; lean_object* v_err_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v_pos_2107_ = lean_ctor_get(v___x_2096_, 0);
v_err_2108_ = lean_ctor_get(v___x_2096_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2096_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_err_2108_);
lean_inc(v_pos_2107_);
lean_dec(v___x_2096_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_pos_2107_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_err_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
v___jp_2116_:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_2120_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_2122_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2118_, v___x_2121_);
lean_dec(v_res_2118_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2091_, v_pos_2117_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_pos_2124_; lean_object* v_res_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_pos_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_pos_2124_);
v_res_2125_ = lean_ctor_get(v___x_2123_, 1);
lean_inc(v_res_2125_);
lean_dec_ref_known(v___x_2123_, 2);
v___x_2126_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2127_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2126_, v_pos_2124_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_pos_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2136_; 
v_pos_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v___x_2127_, 1);
lean_dec(v_unused_2137_);
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2136_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_pos_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2136_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_res_2125_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v___x_2132_);
v___x_2134_ = v___x_2130_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_pos_2128_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
else
{
lean_object* v_pos_2138_; lean_object* v_err_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_res_2125_);
v_pos_2138_ = lean_ctor_get(v___x_2127_, 0);
v_err_2139_ = lean_ctor_get(v___x_2127_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2127_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_err_2139_);
lean_inc(v_pos_2138_);
lean_dec(v___x_2127_);
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
else
{
lean_object* v_pos_2147_; lean_object* v_err_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_pos_2147_ = lean_ctor_get(v___x_2123_, 0);
v_err_2148_ = lean_ctor_get(v___x_2123_, 1);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2123_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_err_2148_);
lean_inc(v_pos_2147_);
lean_dec(v___x_2123_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_pos_2147_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_err_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
v___y_2094_ = v_pos_2117_;
goto v___jp_2093_;
}
}
else
{
lean_dec(v_res_2118_);
v___y_2094_ = v_pos_2117_;
goto v___jp_2093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2164_, v_a_2165_);
lean_dec_ref(v_limits_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2171_){
_start:
{
lean_object* v_array_2172_; lean_object* v_idx_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_array_2172_ = lean_ctor_get(v_a_2171_, 0);
v_idx_2173_ = lean_ctor_get(v_a_2171_, 1);
v___x_2174_ = lean_byte_array_size(v_array_2172_);
v___x_2175_ = lean_nat_dec_lt(v_idx_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_box(0);
v___x_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2177_, 0, v_a_2171_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
return v___x_2177_;
}
else
{
uint8_t v___x_2178_; uint8_t v_got_2179_; uint8_t v___x_2180_; 
v___x_2178_ = 92;
v_got_2179_ = lean_byte_array_fget(v_array_2172_, v_idx_2173_);
v___x_2180_ = lean_uint8_dec_eq(v_got_2179_, v___x_2178_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_a_2171_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
return v___x_2182_;
}
else
{
lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2216_; 
lean_inc(v_idx_2173_);
lean_inc_ref(v_array_2172_);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_a_2171_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; lean_object* v_unused_2218_; 
v_unused_2217_ = lean_ctor_get(v_a_2171_, 1);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_a_2171_, 0);
lean_dec(v_unused_2218_);
v___x_2184_ = v_a_2171_;
v_isShared_2185_ = v_isSharedCheck_2216_;
goto v_resetjp_2183_;
}
else
{
lean_dec(v_a_2171_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2216_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_add(v_idx_2173_, v___x_2186_);
lean_dec(v_idx_2173_);
v___x_2188_ = lean_nat_dec_lt(v___x_2187_, v___x_2174_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2190_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v___x_2187_);
v___x_2190_ = v___x_2184_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_array_2172_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2187_);
v___x_2190_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
return v___x_2192_;
}
}
else
{
uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2194_ = lean_byte_array_fget(v_array_2172_, v___x_2187_);
v___x_2195_ = lean_nat_add(v___x_2187_, v___x_2186_);
lean_dec(v___x_2187_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v___x_2195_);
v___x_2197_ = v___x_2184_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_array_2172_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint32_t v___x_2200_; uint32_t v___x_2207_; uint8_t v___x_2208_; 
v___x_2198_ = lean_box(v___x_2194_);
lean_inc_ref(v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_uint8_to_uint32(v___x_2194_);
v___x_2207_ = 9;
v___x_2208_ = lean_uint32_dec_eq(v___x_2200_, v___x_2207_);
if (v___x_2208_ == 0)
{
uint32_t v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = 32;
v___x_2210_ = lean_uint32_dec_eq(v___x_2200_, v___x_2209_);
if (v___x_2210_ == 0)
{
uint32_t v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = 33;
v___x_2212_ = lean_uint32_dec_le(v___x_2211_, v___x_2200_);
if (v___x_2212_ == 0)
{
lean_dec_ref_known(v___x_2199_, 2);
goto v___jp_2201_;
}
else
{
uint32_t v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = 126;
v___x_2214_ = lean_uint32_dec_le(v___x_2200_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_dec_ref_known(v___x_2199_, 2);
goto v___jp_2201_;
}
else
{
lean_dec_ref(v___x_2197_);
return v___x_2199_;
}
}
}
else
{
lean_dec_ref(v___x_2197_);
return v___x_2199_;
}
}
else
{
lean_dec_ref(v___x_2197_);
return v___x_2199_;
}
v___jp_2201_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2202_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2203_ = l_Char_quote(v___x_2200_);
v___x_2204_ = lean_string_append(v___x_2202_, v___x_2203_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2197_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
return v___x_2206_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2223_, lean_object* v_buf_2224_, lean_object* v_length_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_array_2227_; lean_object* v_idx_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v_array_2227_ = lean_ctor_get(v_a_2226_, 0);
v_idx_2228_ = lean_ctor_get(v_a_2226_, 1);
v___x_2229_ = lean_byte_array_size(v_array_2227_);
v___x_2230_ = lean_nat_dec_lt(v_idx_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_dec(v_length_2225_);
lean_dec_ref(v_buf_2224_);
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2232_, 0, v_a_2226_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
return v___x_2232_;
}
else
{
lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2305_; 
lean_inc(v_idx_2228_);
lean_inc_ref(v_array_2227_);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_a_2226_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; lean_object* v_unused_2307_; 
v_unused_2306_ = lean_ctor_get(v_a_2226_, 1);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_a_2226_, 0);
lean_dec(v_unused_2307_);
v___x_2234_ = v_a_2226_;
v_isShared_2235_ = v_isSharedCheck_2305_;
goto v_resetjp_2233_;
}
else
{
lean_dec(v_a_2226_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2305_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
uint8_t v_c_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v_it_x27_2240_; 
v_c_2236_ = lean_byte_array_fget(v_array_2227_, v_idx_2228_);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v_idx_2228_, v___x_2237_);
lean_dec(v_idx_2228_);
lean_inc(v___x_2238_);
lean_inc_ref(v_array_2227_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v___x_2238_);
v_it_x27_2240_ = v___x_2234_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_array_2227_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v___x_2238_);
v_it_x27_2240_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
uint8_t v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = 34;
v___x_2256_ = lean_uint8_dec_eq(v_c_2236_, v___x_2255_);
if (v___x_2256_ == 0)
{
uint8_t v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = 92;
v___x_2258_ = lean_uint8_dec_eq(v_c_2236_, v___x_2257_);
if (v___x_2258_ == 0)
{
uint32_t v___x_2259_; uint32_t v___x_2265_; uint8_t v___x_2266_; 
lean_dec(v___x_2238_);
lean_dec_ref(v_array_2227_);
v___x_2259_ = lean_uint8_to_uint32(v_c_2236_);
v___x_2265_ = 9;
v___x_2266_ = lean_uint32_dec_eq(v___x_2259_, v___x_2265_);
if (v___x_2266_ == 0)
{
uint32_t v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = 32;
v___x_2268_ = lean_uint32_dec_eq(v___x_2259_, v___x_2267_);
if (v___x_2268_ == 0)
{
uint32_t v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = 33;
v___x_2270_ = lean_uint32_dec_eq(v___x_2259_, v___x_2269_);
if (v___x_2270_ == 0)
{
uint32_t v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = 35;
v___x_2272_ = lean_uint32_dec_le(v___x_2271_, v___x_2259_);
if (v___x_2272_ == 0)
{
goto v___jp_2260_;
}
else
{
uint32_t v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = 91;
v___x_2274_ = lean_uint32_dec_le(v___x_2259_, v___x_2273_);
if (v___x_2274_ == 0)
{
goto v___jp_2260_;
}
else
{
goto v___jp_2241_;
}
}
}
else
{
goto v___jp_2241_;
}
}
else
{
goto v___jp_2241_;
}
}
else
{
goto v___jp_2241_;
}
v___jp_2260_:
{
uint32_t v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = 93;
v___x_2262_ = lean_uint32_dec_le(v___x_2261_, v___x_2259_);
if (v___x_2262_ == 0)
{
lean_dec(v_length_2225_);
lean_dec_ref(v_buf_2224_);
goto v___jp_2248_;
}
else
{
uint32_t v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = 126;
v___x_2264_ = lean_uint32_dec_le(v___x_2259_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_dec(v_length_2225_);
lean_dec_ref(v_buf_2224_);
goto v___jp_2248_;
}
else
{
goto v___jp_2241_;
}
}
}
}
else
{
uint8_t v___x_2275_; 
v___x_2275_ = lean_nat_dec_lt(v___x_2238_, v___x_2229_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec(v___x_2238_);
lean_dec_ref(v_array_2227_);
lean_dec(v_length_2225_);
lean_dec_ref(v_buf_2224_);
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2277_, 0, v_it_x27_2240_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
return v___x_2277_;
}
else
{
uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint32_t v___x_2288_; uint32_t v___x_2295_; uint8_t v___x_2296_; 
lean_dec_ref(v_it_x27_2240_);
v___x_2278_ = lean_byte_array_fget(v_array_2227_, v___x_2238_);
v___x_2279_ = lean_nat_add(v___x_2238_, v___x_2237_);
lean_dec(v___x_2238_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v_array_2227_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2288_ = lean_uint8_to_uint32(v___x_2278_);
v___x_2295_ = 9;
v___x_2296_ = lean_uint32_dec_eq(v___x_2288_, v___x_2295_);
if (v___x_2296_ == 0)
{
uint32_t v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = 32;
v___x_2298_ = lean_uint32_dec_eq(v___x_2288_, v___x_2297_);
if (v___x_2298_ == 0)
{
uint32_t v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = 33;
v___x_2300_ = lean_uint32_dec_le(v___x_2299_, v___x_2288_);
if (v___x_2300_ == 0)
{
lean_dec(v_length_2225_);
lean_dec_ref(v_buf_2224_);
goto v___jp_2289_;
}
else
{
uint32_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = 126;
v___x_2302_ = lean_uint32_dec_le(v___x_2288_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_dec(v_length_2225_);
lean_dec_ref(v_buf_2224_);
goto v___jp_2289_;
}
else
{
goto v___jp_2281_;
}
}
}
else
{
goto v___jp_2281_;
}
}
else
{
goto v___jp_2281_;
}
v___jp_2281_:
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = lean_nat_add(v_length_2225_, v___x_2237_);
lean_dec(v_length_2225_);
v___x_2283_ = lean_nat_dec_lt(v_maxLength_2223_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_byte_array_push(v_buf_2224_, v___x_2278_);
v_buf_2224_ = v___x_2284_;
v_length_2225_ = v___x_2282_;
v_a_2226_ = v___x_2280_;
goto _start;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec(v___x_2282_);
lean_dec_ref(v_buf_2224_);
v___x_2286_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2280_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
return v___x_2287_;
}
}
v___jp_2289_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2290_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2291_ = l_Char_quote(v___x_2288_);
v___x_2292_ = lean_string_append(v___x_2290_, v___x_2291_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2280_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
return v___x_2294_;
}
}
}
}
else
{
lean_object* v___x_2303_; 
lean_dec(v___x_2238_);
lean_dec_ref(v_array_2227_);
lean_dec(v_length_2225_);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v_it_x27_2240_);
lean_ctor_set(v___x_2303_, 1, v_buf_2224_);
return v___x_2303_;
}
v___jp_2241_:
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = lean_nat_add(v_length_2225_, v___x_2237_);
lean_dec(v_length_2225_);
v___x_2243_ = lean_nat_dec_lt(v_maxLength_2223_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_byte_array_push(v_buf_2224_, v_c_2236_);
v_buf_2224_ = v___x_2244_;
v_length_2225_ = v___x_2242_;
v_a_2226_ = v_it_x27_2240_;
goto _start;
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_dec(v___x_2242_);
lean_dec_ref(v_buf_2224_);
v___x_2246_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_it_x27_2240_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
return v___x_2247_;
}
}
v___jp_2248_:
{
lean_object* v___x_2249_; uint32_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2249_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2250_ = lean_uint8_to_uint32(v_c_2236_);
v___x_2251_ = l_Char_quote(v___x_2250_);
v___x_2252_ = lean_string_append(v___x_2249_, v___x_2251_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
v___x_2254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2254_, 0, v_it_x27_2240_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
return v___x_2254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2308_, lean_object* v_buf_2309_, lean_object* v_length_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2308_, v_buf_2309_, v_length_2310_, v_a_2311_);
lean_dec(v_maxLength_2308_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_array_2318_; lean_object* v_idx_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_array_2318_ = lean_ctor_get(v_a_2317_, 0);
v_idx_2319_ = lean_ctor_get(v_a_2317_, 1);
v___x_2320_ = lean_byte_array_size(v_array_2318_);
v___x_2321_ = lean_nat_dec_lt(v_idx_2319_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2317_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
return v___x_2323_;
}
else
{
uint8_t v___x_2324_; uint8_t v_got_2325_; uint8_t v___x_2326_; 
v___x_2324_ = 34;
v_got_2325_ = lean_byte_array_fget(v_array_2318_, v_idx_2319_);
v___x_2326_ = lean_uint8_dec_eq(v_got_2325_, v___x_2324_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_a_2317_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
return v___x_2328_;
}
else
{
lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2357_; 
lean_inc(v_idx_2319_);
lean_inc_ref(v_array_2318_);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_a_2317_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; lean_object* v_unused_2359_; 
v_unused_2358_ = lean_ctor_get(v_a_2317_, 1);
lean_dec(v_unused_2358_);
v_unused_2359_ = lean_ctor_get(v_a_2317_, 0);
lean_dec(v_unused_2359_);
v___x_2330_ = v_a_2317_;
v_isShared_2331_ = v_isSharedCheck_2357_;
goto v_resetjp_2329_;
}
else
{
lean_dec(v_a_2317_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2357_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_nat_add(v_idx_2319_, v___x_2332_);
lean_dec(v_idx_2319_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 1, v___x_2333_);
v___x_2335_ = v___x_2330_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_array_2318_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = l_ByteArray_empty;
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2316_, v___x_2336_, v___x_2337_, v___x_2335_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_pos_2339_; lean_object* v_res_2340_; uint8_t v___x_2341_; 
v_pos_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_pos_2339_);
v_res_2340_ = lean_ctor_get(v___x_2338_, 1);
lean_inc(v_res_2340_);
lean_dec_ref_known(v___x_2338_, 2);
v___x_2341_ = lean_string_validate_utf8(v_res_2340_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec(v_res_2340_);
v___x_2342_ = lean_box(0);
v___x_2343_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2342_, v_pos_2339_);
return v___x_2343_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = lean_string_from_utf8_unchecked(v_res_2340_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
v___x_2346_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2345_, v_pos_2339_);
lean_dec_ref_known(v___x_2345_, 1);
return v___x_2346_;
}
}
else
{
lean_object* v_pos_2347_; lean_object* v_err_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
v_pos_2347_ = lean_ctor_get(v___x_2338_, 0);
v_err_2348_ = lean_ctor_get(v___x_2338_, 1);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2338_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_err_2348_);
lean_inc(v_pos_2347_);
lean_dec(v___x_2338_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_pos_2347_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_err_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_2360_, v_a_2361_);
lean_dec(v_maxLength_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_2363_, lean_object* v_maxSpaceSequence_2364_, lean_object* v_x_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_pos_2368_; lean_object* v_pos_2372_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_snd_2377_; lean_object* v_snd_2378_; uint8_t v___x_2379_; 
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2363_, v_maxSpaceSequence_2364_, v___x_2375_, v___y_2366_);
v_snd_2377_ = lean_ctor_get(v___x_2376_, 1);
lean_inc(v_snd_2377_);
lean_dec_ref(v___x_2376_);
v_snd_2378_ = lean_ctor_get(v_snd_2377_, 1);
v___x_2379_ = lean_unbox(v_snd_2378_);
if (v___x_2379_ == 0)
{
lean_object* v_fst_2380_; lean_object* v_array_2381_; lean_object* v_idx_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_fst_2380_ = lean_ctor_get(v_snd_2377_, 0);
lean_inc(v_fst_2380_);
lean_dec(v_snd_2377_);
v_array_2381_ = lean_ctor_get(v_fst_2380_, 0);
v_idx_2382_ = lean_ctor_get(v_fst_2380_, 1);
v___x_2383_ = lean_byte_array_size(v_array_2381_);
v___x_2384_ = lean_nat_dec_lt(v_idx_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
v_pos_2368_ = v_fst_2380_;
goto v___jp_2367_;
}
else
{
uint8_t v___x_2385_; uint32_t v___x_2386_; uint32_t v___x_2387_; uint8_t v___x_2388_; 
v___x_2385_ = lean_byte_array_fget(v_array_2381_, v_idx_2382_);
v___x_2386_ = lean_uint8_to_uint32(v___x_2385_);
v___x_2387_ = 32;
v___x_2388_ = lean_uint32_dec_eq(v___x_2386_, v___x_2387_);
if (v___x_2388_ == 0)
{
uint32_t v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = 9;
v___x_2390_ = lean_uint32_dec_eq(v___x_2386_, v___x_2389_);
if (v___x_2390_ == 0)
{
v_pos_2368_ = v_fst_2380_;
goto v___jp_2367_;
}
else
{
v_pos_2372_ = v_fst_2380_;
goto v___jp_2371_;
}
}
else
{
v_pos_2372_ = v_fst_2380_;
goto v___jp_2371_;
}
}
}
else
{
lean_object* v_fst_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
v_fst_2391_ = lean_ctor_get(v_snd_2377_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_snd_2377_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v_snd_2377_, 1);
lean_dec(v_unused_2400_);
v___x_2393_ = v_snd_2377_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_fst_2391_);
lean_dec(v_snd_2377_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = lean_box(0);
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 1);
lean_ctor_set(v___x_2393_, 1, v___x_2395_);
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_fst_2391_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
v___jp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_pos_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
return v___x_2370_;
}
v___jp_2371_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_pos_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_2401_, lean_object* v_maxSpaceSequence_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2401_, v_maxSpaceSequence_2402_, v_x_2403_, v___y_2404_);
lean_dec(v_maxSpaceSequence_2402_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_pos_2421_; lean_object* v_pos_2425_; lean_object* v___y_2429_; lean_object* v_pos_2430_; lean_object* v___y_2435_; lean_object* v_pos_2436_; lean_object* v_res_2437_; lean_object* v___y_2444_; lean_object* v_pos_2445_; lean_object* v_res_2446_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v_lower_2463_; lean_object* v_upper_2464_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v_pos_2480_; lean_object* v_pos_2484_; lean_object* v_maxSpaceSequence_2487_; lean_object* v_maxChunkExtNameLength_2488_; lean_object* v_maxChunkExtValueLength_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v_snd_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2785_; 
v_maxSpaceSequence_2487_ = lean_ctor_get(v_limits_2418_, 8);
v_maxChunkExtNameLength_2488_ = lean_ctor_get(v_limits_2418_, 11);
v_maxChunkExtValueLength_2489_ = lean_ctor_get(v_limits_2418_, 12);
v___f_2490_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__2));
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2490_, v_maxSpaceSequence_2487_, v___x_2491_, v_a_2419_);
v_snd_2493_ = lean_ctor_get(v___x_2492_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v___x_2492_, 0);
lean_dec(v_unused_2786_);
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2785_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_snd_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2785_;
goto v_resetjp_2494_;
}
v___jp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_pos_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
return v___x_2423_;
}
v___jp_2424_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_pos_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
return v___x_2427_;
}
v___jp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___y_2429_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_pos_2430_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
return v___x_2433_;
}
v___jp_2434_:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_2437_);
if (lean_obj_tag(v___x_2438_) == 1)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___y_2435_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_pos_2436_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec(v___x_2438_);
lean_dec_ref(v___y_2435_);
v___x_2441_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
v___x_2442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_pos_2436_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
return v___x_2442_;
}
}
v___jp_2443_:
{
lean_object* v___x_2447_; 
v___x_2447_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2446_, v_pos_2445_);
lean_dec(v_res_2446_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_pos_2448_; lean_object* v_res_2449_; 
v_pos_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_pos_2448_);
v_res_2449_ = lean_ctor_get(v___x_2447_, 1);
lean_inc(v_res_2449_);
lean_dec_ref_known(v___x_2447_, 2);
v___y_2435_ = v___y_2444_;
v_pos_2436_ = v_pos_2448_;
v_res_2437_ = v_res_2449_;
goto v___jp_2434_;
}
else
{
lean_object* v_pos_2450_; lean_object* v_err_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v___y_2444_);
v_pos_2450_ = lean_ctor_get(v___x_2447_, 0);
v_err_2451_ = lean_ctor_get(v___x_2447_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2447_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_err_2451_);
lean_inc(v_pos_2450_);
lean_dec(v___x_2447_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_pos_2450_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_err_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
v___jp_2459_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2465_ = l_ByteArray_toByteSlice(v___y_2461_, v_lower_2463_, v_upper_2464_);
v___x_2466_ = l_ByteSlice_toByteArray(v___x_2465_);
v___x_2467_ = lean_string_validate_utf8(v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_dec_ref(v___x_2466_);
v___x_2468_ = lean_box(0);
v___y_2444_ = v___y_2462_;
v_pos_2445_ = v___y_2460_;
v_res_2446_ = v___x_2468_;
goto v___jp_2443_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_string_from_utf8_unchecked(v___x_2466_);
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
v___y_2444_ = v___y_2462_;
v_pos_2445_ = v___y_2460_;
v_res_2446_ = v___x_2470_;
goto v___jp_2443_;
}
}
v___jp_2471_:
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_le(v___y_2472_, v___y_2476_);
if (v___x_2478_ == 0)
{
lean_dec(v___y_2472_);
v___y_2460_ = v___y_2474_;
v___y_2461_ = v___y_2473_;
v___y_2462_ = v___y_2475_;
v_lower_2463_ = v___y_2477_;
v_upper_2464_ = v___y_2476_;
goto v___jp_2459_;
}
else
{
lean_dec(v___y_2476_);
v___y_2460_ = v___y_2474_;
v___y_2461_ = v___y_2473_;
v___y_2462_ = v___y_2475_;
v_lower_2463_ = v___y_2477_;
v_upper_2464_ = v___y_2472_;
goto v___jp_2459_;
}
}
v___jp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_pos_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
return v___x_2482_;
}
v___jp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_pos_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
return v___x_2486_;
}
v_resetjp_2494_:
{
lean_object* v_snd_2497_; uint8_t v___x_2498_; 
v_snd_2497_ = lean_ctor_get(v_snd_2493_, 1);
v___x_2498_ = lean_unbox(v_snd_2497_);
if (v___x_2498_ == 0)
{
lean_object* v_fst_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2773_; 
v_fst_2499_ = lean_ctor_get(v_snd_2493_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_snd_2493_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; 
v_unused_2774_ = lean_ctor_get(v_snd_2493_, 1);
lean_dec(v_unused_2774_);
v___x_2501_ = v_snd_2493_;
v_isShared_2502_ = v_isSharedCheck_2773_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_fst_2499_);
lean_dec(v_snd_2493_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2773_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_array_2503_; lean_object* v_idx_2504_; lean_object* v___f_2505_; lean_object* v___y_2507_; lean_object* v_pos_2508_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v_pos_2547_; lean_object* v_array_2548_; lean_object* v_idx_2549_; lean_object* v_pos_2605_; lean_object* v_res_2606_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v_lower_2672_; lean_object* v_upper_2673_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v_pos_2688_; lean_object* v_pos_2721_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v_array_2503_ = lean_ctor_get(v_fst_2499_, 0);
v_idx_2504_ = lean_ctor_get(v_fst_2499_, 1);
v___f_2505_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2765_ = lean_byte_array_size(v_array_2503_);
v___x_2766_ = lean_nat_dec_lt(v_idx_2504_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_inc(v_idx_2504_);
lean_inc_ref(v_array_2503_);
v_pos_2721_ = v_fst_2499_;
goto v___jp_2720_;
}
else
{
uint8_t v___x_2767_; uint32_t v___x_2768_; uint32_t v___x_2769_; uint8_t v___x_2770_; 
v___x_2767_ = lean_byte_array_fget(v_array_2503_, v_idx_2504_);
v___x_2768_ = lean_uint8_to_uint32(v___x_2767_);
v___x_2769_ = 32;
v___x_2770_ = lean_uint32_dec_eq(v___x_2768_, v___x_2769_);
if (v___x_2770_ == 0)
{
uint32_t v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = 9;
v___x_2772_ = lean_uint32_dec_eq(v___x_2768_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_inc(v_idx_2504_);
lean_inc_ref(v_array_2503_);
v_pos_2721_ = v_fst_2499_;
goto v___jp_2720_;
}
else
{
lean_del_object(v___x_2501_);
lean_del_object(v___x_2495_);
v_pos_2421_ = v_fst_2499_;
goto v___jp_2420_;
}
}
else
{
lean_del_object(v___x_2501_);
lean_del_object(v___x_2495_);
v_pos_2421_ = v_fst_2499_;
goto v___jp_2420_;
}
}
v___jp_2506_:
{
lean_object* v___x_2509_; 
lean_inc_ref(v_pos_2508_);
v___x_2509_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_2489_, v_pos_2508_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_pos_2510_; lean_object* v_res_2511_; 
lean_dec_ref(v_pos_2508_);
v_pos_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_pos_2510_);
v_res_2511_ = lean_ctor_get(v___x_2509_, 1);
lean_inc(v_res_2511_);
lean_dec_ref_known(v___x_2509_, 2);
v___y_2435_ = v___y_2507_;
v_pos_2436_ = v_pos_2510_;
v_res_2437_ = v_res_2511_;
goto v___jp_2434_;
}
else
{
lean_object* v_pos_2512_; lean_object* v_err_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2543_; 
v_pos_2512_ = lean_ctor_get(v___x_2509_, 0);
v_err_2513_ = lean_ctor_get(v___x_2509_, 1);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2515_ = v___x_2509_;
v_isShared_2516_ = v_isSharedCheck_2543_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_err_2513_);
lean_inc(v_pos_2512_);
lean_dec(v___x_2509_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2543_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_idx_2517_; lean_object* v_array_2518_; lean_object* v_idx_2519_; uint8_t v___x_2520_; 
v_idx_2517_ = lean_ctor_get(v_pos_2508_, 1);
lean_inc(v_idx_2517_);
lean_dec_ref(v_pos_2508_);
v_array_2518_ = lean_ctor_get(v_pos_2512_, 0);
v_idx_2519_ = lean_ctor_get(v_pos_2512_, 1);
v___x_2520_ = lean_nat_dec_eq(v_idx_2517_, v_idx_2519_);
lean_dec(v_idx_2517_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref(v___y_2507_);
if (v_isShared_2516_ == 0)
{
v___x_2522_ = v___x_2515_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_pos_2512_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_err_2513_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
else
{
lean_object* v___x_2524_; lean_object* v_snd_2525_; lean_object* v_snd_2526_; uint8_t v___x_2527_; 
lean_dec(v_err_2513_);
lean_inc(v_pos_2512_);
v___x_2524_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2505_, v_maxChunkExtValueLength_2489_, v___x_2491_, v_pos_2512_);
v_snd_2525_ = lean_ctor_get(v___x_2524_, 1);
lean_inc(v_snd_2525_);
v_snd_2526_ = lean_ctor_get(v_snd_2525_, 1);
v___x_2527_ = lean_unbox(v_snd_2526_);
if (v___x_2527_ == 0)
{
lean_object* v_fst_2528_; lean_object* v_fst_2529_; uint8_t v___x_2530_; 
v_fst_2528_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_fst_2528_);
lean_dec_ref(v___x_2524_);
v_fst_2529_ = lean_ctor_get(v_snd_2525_, 0);
lean_inc(v_fst_2529_);
lean_dec(v_snd_2525_);
v___x_2530_ = lean_nat_dec_eq(v_fst_2528_, v___x_2491_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
lean_inc(v_idx_2519_);
lean_inc_ref(v_array_2518_);
lean_del_object(v___x_2515_);
lean_dec(v_pos_2512_);
v___x_2531_ = lean_nat_add(v_idx_2519_, v_fst_2528_);
lean_dec(v_fst_2528_);
v___x_2532_ = lean_byte_array_size(v_array_2518_);
v___x_2533_ = lean_nat_dec_le(v_idx_2519_, v___x_2491_);
if (v___x_2533_ == 0)
{
v___y_2472_ = v___x_2531_;
v___y_2473_ = v_array_2518_;
v___y_2474_ = v_fst_2529_;
v___y_2475_ = v___y_2507_;
v___y_2476_ = v___x_2532_;
v___y_2477_ = v_idx_2519_;
goto v___jp_2471_;
}
else
{
lean_dec(v_idx_2519_);
v___y_2472_ = v___x_2531_;
v___y_2473_ = v_array_2518_;
v___y_2474_ = v_fst_2529_;
v___y_2475_ = v___y_2507_;
v___y_2476_ = v___x_2532_;
v___y_2477_ = v___x_2491_;
goto v___jp_2471_;
}
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_dec(v_fst_2529_);
lean_dec(v_fst_2528_);
lean_dec_ref(v___y_2507_);
v___x_2534_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 1, v___x_2534_);
v___x_2536_ = v___x_2515_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_pos_2512_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
else
{
lean_object* v_fst_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_dec_ref(v___x_2524_);
lean_dec(v_pos_2512_);
lean_dec_ref(v___y_2507_);
v_fst_2538_ = lean_ctor_get(v_snd_2525_, 0);
lean_inc(v_fst_2538_);
lean_dec(v_snd_2525_);
v___x_2539_ = lean_box(0);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 1, v___x_2539_);
lean_ctor_set(v___x_2515_, 0, v_fst_2538_);
v___x_2541_ = v___x_2515_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_fst_2538_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
v___jp_2544_:
{
lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2550_ = lean_byte_array_size(v_array_2548_);
v___x_2551_ = lean_nat_dec_lt(v_idx_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
lean_dec(v_idx_2549_);
lean_dec_ref(v_array_2548_);
lean_dec_ref(v___y_2546_);
v___x_2552_ = lean_box(0);
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 1);
lean_ctor_set(v___x_2501_, 1, v___x_2552_);
lean_ctor_set(v___x_2501_, 0, v_pos_2547_);
v___x_2554_ = v___x_2501_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_pos_2547_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
else
{
uint8_t v___x_2556_; uint8_t v_got_2557_; uint8_t v___x_2558_; 
v___x_2556_ = 61;
v_got_2557_ = lean_byte_array_fget(v_array_2548_, v_idx_2549_);
v___x_2558_ = lean_uint8_dec_eq(v_got_2557_, v___x_2556_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
lean_dec(v_idx_2549_);
lean_dec_ref(v_array_2548_);
lean_dec_ref(v___y_2546_);
v___x_2559_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 1);
lean_ctor_set(v___x_2501_, 1, v___x_2559_);
lean_ctor_set(v___x_2501_, 0, v_pos_2547_);
v___x_2561_ = v___x_2501_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_pos_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
lean_dec_ref(v_pos_2547_);
v___x_2563_ = lean_unsigned_to_nat(1u);
v___x_2564_ = lean_nat_add(v_idx_2549_, v___x_2563_);
lean_dec(v_idx_2549_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2564_);
lean_ctor_set(v___x_2501_, 0, v_array_2548_);
v___x_2566_ = v___x_2501_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_array_2548_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2567_; 
v___x_2567_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2490_, v_maxSpaceSequence_2487_, v___y_2545_, v___x_2566_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_pos_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2592_; 
v_pos_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2592_ == 0)
{
lean_object* v_unused_2593_; 
v_unused_2593_ = lean_ctor_get(v___x_2567_, 1);
lean_dec(v_unused_2593_);
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2592_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_pos_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2592_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v_snd_2573_; lean_object* v_snd_2574_; uint8_t v___x_2575_; 
v___x_2572_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2490_, v_maxSpaceSequence_2487_, v___x_2491_, v_pos_2568_);
v_snd_2573_ = lean_ctor_get(v___x_2572_, 1);
lean_inc(v_snd_2573_);
lean_dec_ref(v___x_2572_);
v_snd_2574_ = lean_ctor_get(v_snd_2573_, 1);
v___x_2575_ = lean_unbox(v_snd_2574_);
if (v___x_2575_ == 0)
{
lean_object* v_fst_2576_; lean_object* v_array_2577_; lean_object* v_idx_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
lean_del_object(v___x_2570_);
v_fst_2576_ = lean_ctor_get(v_snd_2573_, 0);
lean_inc(v_fst_2576_);
lean_dec(v_snd_2573_);
v_array_2577_ = lean_ctor_get(v_fst_2576_, 0);
v_idx_2578_ = lean_ctor_get(v_fst_2576_, 1);
v___x_2579_ = lean_byte_array_size(v_array_2577_);
v___x_2580_ = lean_nat_dec_lt(v_idx_2578_, v___x_2579_);
if (v___x_2580_ == 0)
{
v___y_2507_ = v___y_2546_;
v_pos_2508_ = v_fst_2576_;
goto v___jp_2506_;
}
else
{
uint8_t v___x_2581_; uint32_t v___x_2582_; uint32_t v___x_2583_; uint8_t v___x_2584_; 
v___x_2581_ = lean_byte_array_fget(v_array_2577_, v_idx_2578_);
v___x_2582_ = lean_uint8_to_uint32(v___x_2581_);
v___x_2583_ = 32;
v___x_2584_ = lean_uint32_dec_eq(v___x_2582_, v___x_2583_);
if (v___x_2584_ == 0)
{
uint32_t v___x_2585_; uint8_t v___x_2586_; 
v___x_2585_ = 9;
v___x_2586_ = lean_uint32_dec_eq(v___x_2582_, v___x_2585_);
if (v___x_2586_ == 0)
{
v___y_2507_ = v___y_2546_;
v_pos_2508_ = v_fst_2576_;
goto v___jp_2506_;
}
else
{
lean_dec_ref(v___y_2546_);
v_pos_2480_ = v_fst_2576_;
goto v___jp_2479_;
}
}
else
{
lean_dec_ref(v___y_2546_);
v_pos_2480_ = v_fst_2576_;
goto v___jp_2479_;
}
}
}
else
{
lean_object* v_fst_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_dec_ref(v___y_2546_);
v_fst_2587_ = lean_ctor_get(v_snd_2573_, 0);
lean_inc(v_fst_2587_);
lean_dec(v_snd_2573_);
v___x_2588_ = lean_box(0);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 1);
lean_ctor_set(v___x_2570_, 1, v___x_2588_);
lean_ctor_set(v___x_2570_, 0, v_fst_2587_);
v___x_2590_ = v___x_2570_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_fst_2587_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_pos_2594_; lean_object* v_err_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v___y_2546_);
v_pos_2594_ = lean_ctor_get(v___x_2567_, 0);
v_err_2595_ = lean_ctor_get(v___x_2567_, 1);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2567_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_err_2595_);
lean_inc(v_pos_2594_);
lean_dec(v___x_2567_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_pos_2594_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_err_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
}
}
v___jp_2604_:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_2606_, v_pos_2605_);
lean_dec(v_res_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_pos_2608_; lean_object* v_res_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v_pos_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_pos_2608_);
v_res_2609_ = lean_ctor_get(v___x_2607_, 1);
lean_inc(v_res_2609_);
lean_dec_ref_known(v___x_2607_, 2);
v___x_2610_ = lean_box(0);
v___x_2611_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_2490_, v_maxSpaceSequence_2487_, v___x_2610_, v_pos_2608_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_pos_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2649_; 
v_pos_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; 
v_unused_2650_ = lean_ctor_get(v___x_2611_, 1);
lean_dec(v_unused_2650_);
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2649_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_pos_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2649_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_2609_);
if (lean_obj_tag(v___x_2616_) == 1)
{
lean_object* v_val_2617_; lean_object* v_array_2618_; lean_object* v_idx_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_val_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v_array_2618_ = lean_ctor_get(v_pos_2612_, 0);
v_idx_2619_ = lean_ctor_get(v_pos_2612_, 1);
v___x_2620_ = lean_byte_array_size(v_array_2618_);
v___x_2621_ = lean_nat_dec_lt(v_idx_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_del_object(v___x_2614_);
lean_del_object(v___x_2501_);
v___y_2429_ = v_val_2617_;
v_pos_2430_ = v_pos_2612_;
goto v___jp_2428_;
}
else
{
uint8_t v___x_2622_; uint8_t v___x_2623_; uint8_t v___x_2624_; 
v___x_2622_ = lean_byte_array_fget(v_array_2618_, v_idx_2619_);
v___x_2623_ = 61;
v___x_2624_ = lean_uint8_dec_eq(v___x_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_del_object(v___x_2614_);
lean_del_object(v___x_2501_);
v___y_2429_ = v_val_2617_;
v_pos_2430_ = v_pos_2612_;
goto v___jp_2428_;
}
else
{
lean_object* v___x_2625_; lean_object* v_snd_2626_; lean_object* v_snd_2627_; uint8_t v___x_2628_; 
v___x_2625_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2490_, v_maxSpaceSequence_2487_, v___x_2491_, v_pos_2612_);
v_snd_2626_ = lean_ctor_get(v___x_2625_, 1);
lean_inc(v_snd_2626_);
lean_dec_ref(v___x_2625_);
v_snd_2627_ = lean_ctor_get(v_snd_2626_, 1);
v___x_2628_ = lean_unbox(v_snd_2627_);
if (v___x_2628_ == 0)
{
lean_object* v_fst_2629_; lean_object* v_array_2630_; lean_object* v_idx_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
lean_del_object(v___x_2614_);
v_fst_2629_ = lean_ctor_get(v_snd_2626_, 0);
lean_inc(v_fst_2629_);
lean_dec(v_snd_2626_);
v_array_2630_ = lean_ctor_get(v_fst_2629_, 0);
v_idx_2631_ = lean_ctor_get(v_fst_2629_, 1);
v___x_2632_ = lean_byte_array_size(v_array_2630_);
v___x_2633_ = lean_nat_dec_lt(v_idx_2631_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_inc(v_idx_2631_);
lean_inc_ref(v_array_2630_);
v___y_2545_ = v___x_2610_;
v___y_2546_ = v_val_2617_;
v_pos_2547_ = v_fst_2629_;
v_array_2548_ = v_array_2630_;
v_idx_2549_ = v_idx_2631_;
goto v___jp_2544_;
}
else
{
uint8_t v___x_2634_; uint32_t v___x_2635_; uint32_t v___x_2636_; uint8_t v___x_2637_; 
v___x_2634_ = lean_byte_array_fget(v_array_2630_, v_idx_2631_);
v___x_2635_ = lean_uint8_to_uint32(v___x_2634_);
v___x_2636_ = 32;
v___x_2637_ = lean_uint32_dec_eq(v___x_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
uint32_t v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = 9;
v___x_2639_ = lean_uint32_dec_eq(v___x_2635_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_inc(v_idx_2631_);
lean_inc_ref(v_array_2630_);
v___y_2545_ = v___x_2610_;
v___y_2546_ = v_val_2617_;
v_pos_2547_ = v_fst_2629_;
v_array_2548_ = v_array_2630_;
v_idx_2549_ = v_idx_2631_;
goto v___jp_2544_;
}
else
{
lean_dec(v_val_2617_);
lean_del_object(v___x_2501_);
v_pos_2484_ = v_fst_2629_;
goto v___jp_2483_;
}
}
else
{
lean_dec(v_val_2617_);
lean_del_object(v___x_2501_);
v_pos_2484_ = v_fst_2629_;
goto v___jp_2483_;
}
}
}
else
{
lean_object* v_fst_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_dec(v_val_2617_);
lean_del_object(v___x_2501_);
v_fst_2640_ = lean_ctor_get(v_snd_2626_, 0);
lean_inc(v_fst_2640_);
lean_dec(v_snd_2626_);
v___x_2641_ = lean_box(0);
if (v_isShared_2615_ == 0)
{
lean_ctor_set_tag(v___x_2614_, 1);
lean_ctor_set(v___x_2614_, 1, v___x_2641_);
lean_ctor_set(v___x_2614_, 0, v_fst_2640_);
v___x_2643_ = v___x_2614_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_fst_2640_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___x_2641_);
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
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_dec(v___x_2616_);
lean_del_object(v___x_2501_);
v___x_2645_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
if (v_isShared_2615_ == 0)
{
lean_ctor_set_tag(v___x_2614_, 1);
lean_ctor_set(v___x_2614_, 1, v___x_2645_);
v___x_2647_ = v___x_2614_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_pos_2612_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
else
{
lean_object* v_pos_2651_; lean_object* v_err_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_res_2609_);
lean_del_object(v___x_2501_);
v_pos_2651_ = lean_ctor_get(v___x_2611_, 0);
v_err_2652_ = lean_ctor_get(v___x_2611_, 1);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2611_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_err_2652_);
lean_inc(v_pos_2651_);
lean_dec(v___x_2611_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_pos_2651_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_err_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_pos_2660_; lean_object* v_err_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_del_object(v___x_2501_);
v_pos_2660_ = lean_ctor_get(v___x_2607_, 0);
v_err_2661_ = lean_ctor_get(v___x_2607_, 1);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2607_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_err_2661_);
lean_inc(v_pos_2660_);
lean_dec(v___x_2607_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_pos_2660_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_err_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
v___jp_2669_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2674_ = l_ByteArray_toByteSlice(v___y_2670_, v_lower_2672_, v_upper_2673_);
v___x_2675_ = l_ByteSlice_toByteArray(v___x_2674_);
v___x_2676_ = lean_string_validate_utf8(v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
lean_dec_ref(v___x_2675_);
v___x_2677_ = lean_box(0);
v_pos_2605_ = v___y_2671_;
v_res_2606_ = v___x_2677_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = lean_string_from_utf8_unchecked(v___x_2675_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
v_pos_2605_ = v___y_2671_;
v_res_2606_ = v___x_2679_;
goto v___jp_2604_;
}
}
v___jp_2680_:
{
uint8_t v___x_2686_; 
v___x_2686_ = lean_nat_dec_le(v___y_2684_, v___y_2681_);
if (v___x_2686_ == 0)
{
lean_dec(v___y_2684_);
v___y_2670_ = v___y_2682_;
v___y_2671_ = v___y_2683_;
v_lower_2672_ = v___y_2685_;
v_upper_2673_ = v___y_2681_;
goto v___jp_2669_;
}
else
{
lean_dec(v___y_2681_);
v___y_2670_ = v___y_2682_;
v___y_2671_ = v___y_2683_;
v_lower_2672_ = v___y_2685_;
v_upper_2673_ = v___y_2684_;
goto v___jp_2669_;
}
}
v___jp_2687_:
{
lean_object* v___x_2689_; lean_object* v_snd_2690_; lean_object* v_snd_2691_; uint8_t v___x_2692_; 
lean_inc_ref(v_pos_2688_);
v___x_2689_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2505_, v_maxChunkExtNameLength_2488_, v___x_2491_, v_pos_2688_);
v_snd_2690_ = lean_ctor_get(v___x_2689_, 1);
lean_inc(v_snd_2690_);
v_snd_2691_ = lean_ctor_get(v_snd_2690_, 1);
v___x_2692_ = lean_unbox(v_snd_2691_);
if (v___x_2692_ == 0)
{
lean_object* v_fst_2693_; lean_object* v_fst_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2708_; 
v_fst_2693_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_fst_2693_);
lean_dec_ref(v___x_2689_);
v_fst_2694_ = lean_ctor_get(v_snd_2690_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_snd_2690_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v_snd_2690_, 1);
lean_dec(v_unused_2709_);
v___x_2696_ = v_snd_2690_;
v_isShared_2697_ = v_isSharedCheck_2708_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_fst_2694_);
lean_dec(v_snd_2690_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2708_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_nat_dec_eq(v_fst_2693_, v___x_2491_);
if (v___x_2698_ == 0)
{
lean_object* v_array_2699_; lean_object* v_idx_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
lean_del_object(v___x_2696_);
v_array_2699_ = lean_ctor_get(v_pos_2688_, 0);
lean_inc_ref(v_array_2699_);
v_idx_2700_ = lean_ctor_get(v_pos_2688_, 1);
lean_inc(v_idx_2700_);
lean_dec_ref(v_pos_2688_);
v___x_2701_ = lean_nat_add(v_idx_2700_, v_fst_2693_);
lean_dec(v_fst_2693_);
v___x_2702_ = lean_byte_array_size(v_array_2699_);
v___x_2703_ = lean_nat_dec_le(v_idx_2700_, v___x_2491_);
if (v___x_2703_ == 0)
{
v___y_2681_ = v___x_2702_;
v___y_2682_ = v_array_2699_;
v___y_2683_ = v_fst_2694_;
v___y_2684_ = v___x_2701_;
v___y_2685_ = v_idx_2700_;
goto v___jp_2680_;
}
else
{
lean_dec(v_idx_2700_);
v___y_2681_ = v___x_2702_;
v___y_2682_ = v_array_2699_;
v___y_2683_ = v_fst_2694_;
v___y_2684_ = v___x_2701_;
v___y_2685_ = v___x_2491_;
goto v___jp_2680_;
}
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2706_; 
lean_dec(v_fst_2694_);
lean_dec(v_fst_2693_);
lean_del_object(v___x_2501_);
v___x_2704_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 1);
lean_ctor_set(v___x_2696_, 1, v___x_2704_);
lean_ctor_set(v___x_2696_, 0, v_pos_2688_);
v___x_2706_ = v___x_2696_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_pos_2688_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_fst_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v___x_2689_);
lean_dec_ref(v_pos_2688_);
lean_del_object(v___x_2501_);
v_fst_2710_ = lean_ctor_get(v_snd_2690_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_snd_2690_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v_snd_2690_, 1);
lean_dec(v_unused_2719_);
v___x_2712_ = v_snd_2690_;
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_fst_2710_);
lean_dec(v_snd_2690_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2714_ = lean_box(0);
if (v_isShared_2713_ == 0)
{
lean_ctor_set_tag(v___x_2712_, 1);
lean_ctor_set(v___x_2712_, 1, v___x_2714_);
v___x_2716_ = v___x_2712_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_fst_2710_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
v___jp_2720_:
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = lean_byte_array_size(v_array_2503_);
v___x_2723_ = lean_nat_dec_lt(v_idx_2504_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
lean_dec(v_idx_2504_);
lean_dec_ref(v_array_2503_);
lean_del_object(v___x_2501_);
v___x_2724_ = lean_box(0);
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 1);
lean_ctor_set(v___x_2495_, 1, v___x_2724_);
lean_ctor_set(v___x_2495_, 0, v_pos_2721_);
v___x_2726_ = v___x_2495_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_pos_2721_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
else
{
uint8_t v___x_2728_; uint8_t v_got_2729_; uint8_t v___x_2730_; 
v___x_2728_ = 59;
v_got_2729_ = lean_byte_array_fget(v_array_2503_, v_idx_2504_);
v___x_2730_ = lean_uint8_dec_eq(v_got_2729_, v___x_2728_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_dec(v_idx_2504_);
lean_dec_ref(v_array_2503_);
lean_del_object(v___x_2501_);
v___x_2731_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7));
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 1);
lean_ctor_set(v___x_2495_, 1, v___x_2731_);
lean_ctor_set(v___x_2495_, 0, v_pos_2721_);
v___x_2733_ = v___x_2495_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_pos_2721_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_dec_ref(v_pos_2721_);
v___x_2735_ = lean_unsigned_to_nat(1u);
v___x_2736_ = lean_nat_add(v_idx_2504_, v___x_2735_);
lean_dec(v_idx_2504_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v___x_2736_);
lean_ctor_set(v___x_2495_, 0, v_array_2503_);
v___x_2738_ = v___x_2495_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_array_2503_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v_snd_2740_; lean_object* v_snd_2741_; uint8_t v___x_2742_; 
v___x_2739_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2490_, v_maxSpaceSequence_2487_, v___x_2491_, v___x_2738_);
v_snd_2740_ = lean_ctor_get(v___x_2739_, 1);
lean_inc(v_snd_2740_);
lean_dec_ref(v___x_2739_);
v_snd_2741_ = lean_ctor_get(v_snd_2740_, 1);
v___x_2742_ = lean_unbox(v_snd_2741_);
if (v___x_2742_ == 0)
{
lean_object* v_fst_2743_; lean_object* v_array_2744_; lean_object* v_idx_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v_fst_2743_ = lean_ctor_get(v_snd_2740_, 0);
lean_inc(v_fst_2743_);
lean_dec(v_snd_2740_);
v_array_2744_ = lean_ctor_get(v_fst_2743_, 0);
v_idx_2745_ = lean_ctor_get(v_fst_2743_, 1);
v___x_2746_ = lean_byte_array_size(v_array_2744_);
v___x_2747_ = lean_nat_dec_lt(v_idx_2745_, v___x_2746_);
if (v___x_2747_ == 0)
{
v_pos_2688_ = v_fst_2743_;
goto v___jp_2687_;
}
else
{
uint8_t v___x_2748_; uint32_t v___x_2749_; uint32_t v___x_2750_; uint8_t v___x_2751_; 
v___x_2748_ = lean_byte_array_fget(v_array_2744_, v_idx_2745_);
v___x_2749_ = lean_uint8_to_uint32(v___x_2748_);
v___x_2750_ = 32;
v___x_2751_ = lean_uint32_dec_eq(v___x_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
uint32_t v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = 9;
v___x_2753_ = lean_uint32_dec_eq(v___x_2749_, v___x_2752_);
if (v___x_2753_ == 0)
{
v_pos_2688_ = v_fst_2743_;
goto v___jp_2687_;
}
else
{
lean_del_object(v___x_2501_);
v_pos_2425_ = v_fst_2743_;
goto v___jp_2424_;
}
}
else
{
lean_del_object(v___x_2501_);
v_pos_2425_ = v_fst_2743_;
goto v___jp_2424_;
}
}
}
else
{
lean_object* v_fst_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
lean_del_object(v___x_2501_);
v_fst_2754_ = lean_ctor_get(v_snd_2740_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_snd_2740_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v_snd_2740_, 1);
lean_dec(v_unused_2763_);
v___x_2756_ = v_snd_2740_;
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_fst_2754_);
lean_dec(v_snd_2740_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2758_ = lean_box(0);
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 1);
lean_ctor_set(v___x_2756_, 1, v___x_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_fst_2754_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
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
lean_object* v_fst_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2783_; 
lean_del_object(v___x_2495_);
v_fst_2775_ = lean_ctor_get(v_snd_2493_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_snd_2493_);
if (v_isSharedCheck_2783_ == 0)
{
lean_object* v_unused_2784_; 
v_unused_2784_ = lean_ctor_get(v_snd_2493_, 1);
lean_dec(v_unused_2784_);
v___x_2777_ = v_snd_2493_;
v_isShared_2778_ = v_isSharedCheck_2783_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_fst_2775_);
lean_dec(v_snd_2493_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2783_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_box(0);
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 1);
lean_ctor_set(v___x_2777_, 1, v___x_2779_);
v___x_2781_ = v___x_2777_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_fst_2775_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2787_, v_a_2788_);
lean_dec_ref(v_limits_2787_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_pos_2793_; lean_object* v_res_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2802_; 
v_pos_2793_ = lean_ctor_get(v___x_2792_, 0);
v_res_2794_ = lean_ctor_get(v___x_2792_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2796_ = v___x_2792_;
v_isShared_2797_ = v_isSharedCheck_2802_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_res_2794_);
lean_inc(v_pos_2793_);
lean_dec(v___x_2792_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2802_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v_res_2794_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2798_);
v___x_2800_ = v___x_2796_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_pos_2793_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
else
{
lean_object* v_pos_2803_; lean_object* v_err_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_pos_2803_ = lean_ctor_get(v___x_2792_, 0);
v_err_2804_ = lean_ctor_get(v___x_2792_, 1);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2792_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_err_2804_);
lean_inc(v_pos_2803_);
lean_dec(v___x_2792_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_pos_2803_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_err_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_2812_, v___y_2813_);
lean_dec_ref(v_limits_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_2816_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_pos_2818_; lean_object* v_res_2819_; lean_object* v_maxChunkExtensions_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; 
v_pos_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_pos_2818_);
v_res_2819_ = lean_ctor_get(v___x_2817_, 1);
lean_inc(v_res_2819_);
lean_dec_ref_known(v___x_2817_, 2);
v_maxChunkExtensions_2820_ = lean_ctor_get(v_limits_2815_, 10);
lean_inc(v_maxChunkExtensions_2820_);
v___f_2821_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2821_, 0, v_limits_2815_);
v___x_2822_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_2821_, v_maxChunkExtensions_2820_, v_pos_2818_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_pos_2823_; lean_object* v_res_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_pos_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_pos_2823_);
v_res_2824_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_res_2824_);
lean_dec_ref_known(v___x_2822_, 2);
v___x_2825_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2826_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2825_, v_pos_2823_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_pos_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2835_; 
v_pos_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2826_, 1);
lean_dec(v_unused_2836_);
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2835_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_pos_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2835_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_res_2819_);
lean_ctor_set(v___x_2831_, 1, v_res_2824_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v___x_2831_);
v___x_2833_ = v___x_2829_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_pos_2827_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
else
{
lean_object* v_pos_2837_; lean_object* v_err_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_res_2824_);
lean_dec(v_res_2819_);
v_pos_2837_ = lean_ctor_get(v___x_2826_, 0);
v_err_2838_ = lean_ctor_get(v___x_2826_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2826_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_err_2838_);
lean_inc(v_pos_2837_);
lean_dec(v___x_2826_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_pos_2837_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_err_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_pos_2846_; lean_object* v_err_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_res_2819_);
v_pos_2846_ = lean_ctor_get(v___x_2822_, 0);
v_err_2847_ = lean_ctor_get(v___x_2822_, 1);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2822_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_err_2847_);
lean_inc(v_pos_2846_);
lean_dec(v___x_2822_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_pos_2846_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_err_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_pos_2855_; lean_object* v_err_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec_ref(v_limits_2815_);
v_pos_2855_ = lean_ctor_get(v___x_2817_, 0);
v_err_2856_ = lean_ctor_get(v___x_2817_, 1);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2817_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_err_2856_);
lean_inc(v_pos_2855_);
lean_dec(v___x_2817_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_pos_2855_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_err_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object* v_x_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = lean_obj_tag_nat(v_x_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object* v_x_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(v_x_2866_);
lean_dec_ref(v_x_2866_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_2868_, lean_object* v_k_2869_){
_start:
{
if (lean_obj_tag(v_t_2868_) == 0)
{
lean_object* v_data_2870_; lean_object* v___x_2871_; 
v_data_2870_ = lean_ctor_get(v_t_2868_, 0);
lean_inc_ref(v_data_2870_);
lean_dec_ref_known(v_t_2868_, 1);
v___x_2871_ = lean_apply_1(v_k_2869_, v_data_2870_);
return v___x_2871_;
}
else
{
lean_object* v_data_2872_; lean_object* v_remaining_2873_; lean_object* v___x_2874_; 
v_data_2872_ = lean_ctor_get(v_t_2868_, 0);
lean_inc_ref(v_data_2872_);
v_remaining_2873_ = lean_ctor_get(v_t_2868_, 1);
lean_inc(v_remaining_2873_);
lean_dec_ref_known(v_t_2868_, 2);
v___x_2874_ = lean_apply_2(v_k_2869_, v_data_2872_, v_remaining_2873_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_2875_, lean_object* v_ctorIdx_2876_, lean_object* v_t_2877_, lean_object* v_h_2878_, lean_object* v_k_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2877_, v_k_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_2881_, lean_object* v_ctorIdx_2882_, lean_object* v_t_2883_, lean_object* v_h_2884_, lean_object* v_k_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_2881_, v_ctorIdx_2882_, v_t_2883_, v_h_2884_, v_k_2885_);
lean_dec(v_ctorIdx_2882_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_2887_, lean_object* v_complete_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2887_, v_complete_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_2890_, lean_object* v_t_2891_, lean_object* v_h_2892_, lean_object* v_complete_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2891_, v_complete_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_2895_, lean_object* v_incomplete_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2895_, v_incomplete_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_2898_, lean_object* v_t_2899_, lean_object* v_h_2900_, lean_object* v_incomplete_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_2899_, v_incomplete_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_res_2906_; lean_object* v_pos_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2947_; 
v_res_2906_ = lean_ctor_get(v___x_2905_, 1);
v_pos_2907_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2909_ = v___x_2905_;
v_isShared_2910_ = v_isSharedCheck_2947_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_res_2906_);
lean_inc(v_pos_2907_);
lean_dec(v___x_2905_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2947_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_fst_2911_; lean_object* v_snd_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2946_; 
v_fst_2911_ = lean_ctor_get(v_res_2906_, 0);
v_snd_2912_ = lean_ctor_get(v_res_2906_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_res_2906_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2914_ = v_res_2906_;
v_isShared_2915_ = v_isSharedCheck_2946_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_snd_2912_);
lean_inc(v_fst_2911_);
lean_dec(v_res_2906_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2946_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = lean_nat_dec_eq(v_fst_2911_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; 
lean_del_object(v___x_2909_);
v___x_2918_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_2911_, v_pos_2907_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_pos_2919_; lean_object* v_res_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2932_; 
v_pos_2919_ = lean_ctor_get(v___x_2918_, 0);
v_res_2920_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2922_ = v___x_2918_;
v_isShared_2923_ = v_isSharedCheck_2932_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_res_2920_);
lean_inc(v_pos_2919_);
lean_dec(v___x_2918_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2932_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 1, v_res_2920_);
lean_ctor_set(v___x_2914_, 0, v_snd_2912_);
v___x_2925_ = v___x_2914_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_snd_2912_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_res_2920_);
v___x_2925_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v_fst_2911_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v___x_2927_);
v___x_2929_ = v___x_2922_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_pos_2919_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_pos_2933_; lean_object* v_err_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_del_object(v___x_2914_);
lean_dec(v_snd_2912_);
lean_dec(v_fst_2911_);
v_pos_2933_ = lean_ctor_get(v___x_2918_, 0);
v_err_2934_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2918_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_err_2934_);
lean_inc(v_pos_2933_);
lean_dec(v___x_2918_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_pos_2933_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_err_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
lean_del_object(v___x_2914_);
lean_dec(v_snd_2912_);
lean_dec(v_fst_2911_);
v___x_2942_ = lean_box(0);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_2942_);
v___x_2944_ = v___x_2909_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_pos_2907_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
else
{
lean_object* v_pos_2948_; lean_object* v_err_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_pos_2948_ = lean_ctor_get(v___x_2905_, 0);
v_err_2949_ = lean_ctor_get(v___x_2905_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2905_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_err_2949_);
lean_inc(v_pos_2948_);
lean_dec(v___x_2905_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_pos_2948_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_err_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_2957_, lean_object* v_it_2958_){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2959_ = l_ByteArray_Iterator_remainingBytes(v_it_2958_);
v___x_2960_ = lean_unsigned_to_nat(0u);
v___x_2961_ = lean_nat_dec_eq(v___x_2959_, v___x_2960_);
if (v___x_2961_ == 0)
{
uint8_t v___x_2962_; 
v___x_2962_ = lean_nat_dec_lt(v___x_2959_, v_size_2957_);
if (v___x_2962_ == 0)
{
lean_object* v_array_2963_; lean_object* v_idx_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v___x_2959_);
v_array_2963_ = lean_ctor_get(v_it_2958_, 0);
v_idx_2964_ = lean_ctor_get(v_it_2958_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_it_2958_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2966_ = v_it_2958_;
v_isShared_2967_ = v_isSharedCheck_2983_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_idx_2964_);
lean_inc(v_array_2963_);
lean_dec(v_it_2958_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2983_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2968_ = lean_nat_add(v_idx_2964_, v_size_2957_);
lean_inc(v___x_2968_);
lean_inc_ref(v_array_2963_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v___x_2968_);
v___x_2970_ = v___x_2966_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_array_2963_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v_lower_2972_; lean_object* v_upper_2973_; lean_object* v___x_2977_; lean_object* v___y_2979_; uint8_t v___x_2981_; 
v___x_2977_ = lean_byte_array_size(v_array_2963_);
v___x_2981_ = lean_nat_dec_le(v_idx_2964_, v___x_2960_);
if (v___x_2981_ == 0)
{
v___y_2979_ = v_idx_2964_;
goto v___jp_2978_;
}
else
{
lean_dec(v_idx_2964_);
v___y_2979_ = v___x_2960_;
goto v___jp_2978_;
}
v___jp_2971_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = l_ByteArray_toByteSlice(v_array_2963_, v_lower_2972_, v_upper_2973_);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2970_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
return v___x_2976_;
}
v___jp_2978_:
{
uint8_t v___x_2980_; 
v___x_2980_ = lean_nat_dec_le(v___x_2968_, v___x_2977_);
if (v___x_2980_ == 0)
{
lean_dec(v___x_2968_);
v_lower_2972_ = v___y_2979_;
v_upper_2973_ = v___x_2977_;
goto v___jp_2971_;
}
else
{
v_lower_2972_ = v___y_2979_;
v_upper_2973_ = v___x_2968_;
goto v___jp_2971_;
}
}
}
}
}
else
{
lean_object* v_array_2984_; lean_object* v_idx_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3005_; 
v_array_2984_ = lean_ctor_get(v_it_2958_, 0);
v_idx_2985_ = lean_ctor_get(v_it_2958_, 1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_it_2958_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2987_ = v_it_2958_;
v_isShared_2988_ = v_isSharedCheck_3005_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_idx_2985_);
lean_inc(v_array_2984_);
lean_dec(v_it_2958_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3005_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2989_ = lean_nat_add(v_idx_2985_, v___x_2959_);
lean_inc(v___x_2989_);
lean_inc_ref(v_array_2984_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 1, v___x_2989_);
v___x_2991_ = v___x_2987_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_array_2984_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v_lower_2993_; lean_object* v_upper_2994_; lean_object* v___x_2999_; lean_object* v___y_3001_; uint8_t v___x_3003_; 
v___x_2999_ = lean_byte_array_size(v_array_2984_);
v___x_3003_ = lean_nat_dec_le(v_idx_2985_, v___x_2960_);
if (v___x_3003_ == 0)
{
v___y_3001_ = v_idx_2985_;
goto v___jp_3000_;
}
else
{
lean_dec(v_idx_2985_);
v___y_3001_ = v___x_2960_;
goto v___jp_3000_;
}
v___jp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2995_ = l_ByteArray_toByteSlice(v_array_2984_, v_lower_2993_, v_upper_2994_);
v___x_2996_ = lean_nat_sub(v_size_2957_, v___x_2959_);
lean_dec(v___x_2959_);
v___x_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2995_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2991_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
return v___x_2998_;
}
v___jp_3000_:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_nat_dec_le(v___x_2989_, v___x_2999_);
if (v___x_3002_ == 0)
{
lean_dec(v___x_2989_);
v_lower_2993_ = v___y_3001_;
v_upper_2994_ = v___x_2999_;
goto v___jp_2992_;
}
else
{
v_lower_2993_ = v___y_3001_;
v_upper_2994_ = v___x_2989_;
goto v___jp_2992_;
}
}
}
}
}
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec(v___x_2959_);
v___x_3006_ = lean_box(0);
v___x_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3007_, 0, v_it_2958_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
return v___x_3007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3008_, lean_object* v_it_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3008_, v_it_3009_);
lean_dec(v_size_3008_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3011_, v_a_3012_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_res_3014_; 
v_res_3014_ = lean_ctor_get(v___x_3013_, 1);
if (lean_obj_tag(v_res_3014_) == 0)
{
lean_object* v_pos_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_inc_ref(v_res_3014_);
v_pos_3015_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_pos_3015_);
lean_dec_ref_known(v___x_3013_, 2);
v___x_3016_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3017_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3016_, v_pos_3015_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_pos_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
v_pos_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v___x_3017_, 1);
lean_dec(v_unused_3026_);
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_pos_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v_res_3014_);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_pos_3018_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_res_3014_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
else
{
lean_object* v_pos_3027_; lean_object* v_err_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref_known(v_res_3014_, 1);
v_pos_3027_ = lean_ctor_get(v___x_3017_, 0);
v_err_3028_ = lean_ctor_get(v___x_3017_, 1);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3017_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_err_3028_);
lean_inc(v_pos_3027_);
lean_dec(v___x_3017_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_pos_3027_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_err_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
return v___x_3013_;
}
}
else
{
return v___x_3013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3036_, v_a_3037_);
lean_dec(v_size_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(lean_object* v_s_3039_, lean_object* v_p_3040_){
_start:
{
lean_object* v___y_3042_; lean_object* v___y_3043_; uint32_t v___y_3047_; lean_object* v___x_3059_; uint8_t v_decide_3060_; 
v___x_3059_ = lean_string_utf8_byte_size(v_s_3039_);
v_decide_3060_ = lean_nat_dec_eq(v_p_3040_, v___x_3059_);
if (v_decide_3060_ == 0)
{
uint32_t v___x_3061_; uint32_t v___x_3062_; uint8_t v___x_3063_; 
v___x_3061_ = lean_string_utf8_get_fast(v_s_3039_, v_p_3040_);
v___x_3062_ = 65;
v___x_3063_ = lean_uint32_dec_le(v___x_3062_, v___x_3061_);
if (v___x_3063_ == 0)
{
v___y_3047_ = v___x_3061_;
goto v___jp_3046_;
}
else
{
uint32_t v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = 90;
v___x_3065_ = lean_uint32_dec_le(v___x_3061_, v___x_3064_);
if (v___x_3065_ == 0)
{
v___y_3047_ = v___x_3061_;
goto v___jp_3046_;
}
else
{
uint32_t v___x_3066_; uint32_t v___x_3067_; 
v___x_3066_ = 32;
v___x_3067_ = lean_uint32_add(v___x_3061_, v___x_3066_);
v___y_3047_ = v___x_3067_;
goto v___jp_3046_;
}
}
}
else
{
lean_dec(v_p_3040_);
return v_s_3039_;
}
v___jp_3041_:
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_nat_add(v_p_3040_, v___y_3043_);
lean_dec(v_p_3040_);
v_s_3039_ = v___y_3042_;
v_p_3040_ = v___x_3044_;
goto _start;
}
v___jp_3046_:
{
lean_object* v___x_3048_; uint32_t v___x_3049_; uint8_t v___x_3050_; 
lean_inc(v_p_3040_);
v___x_3048_ = lean_string_utf8_set(v_s_3039_, v_p_3040_, v___y_3047_);
v___x_3049_ = 127;
v___x_3050_ = lean_uint32_dec_le(v___y_3047_, v___x_3049_);
if (v___x_3050_ == 0)
{
uint32_t v___x_3051_; uint8_t v___x_3052_; 
v___x_3051_ = 2047;
v___x_3052_ = lean_uint32_dec_le(v___y_3047_, v___x_3051_);
if (v___x_3052_ == 0)
{
uint32_t v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = 65535;
v___x_3054_ = lean_uint32_dec_le(v___y_3047_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_unsigned_to_nat(4u);
v___y_3042_ = v___x_3048_;
v___y_3043_ = v___x_3055_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_unsigned_to_nat(3u);
v___y_3042_ = v___x_3048_;
v___y_3043_ = v___x_3056_;
goto v___jp_3041_;
}
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_unsigned_to_nat(2u);
v___y_3042_ = v___x_3048_;
v___y_3043_ = v___x_3057_;
goto v___jp_3041_;
}
}
else
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_unsigned_to_nat(1u);
v___y_3042_ = v___x_3048_;
v___y_3043_ = v___x_3058_;
goto v___jp_3041_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(lean_object* v_name_3075_){
_start:
{
lean_object* v___x_3076_; lean_object* v_n_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3076_ = lean_unsigned_to_nat(0u);
v_n_3077_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(v_name_3075_, v___x_3076_);
v___x_3078_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__0));
v___x_3079_ = lean_string_dec_eq(v_n_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__1));
v___x_3081_ = lean_string_dec_eq(v_n_3077_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__2));
v___x_3083_ = lean_string_dec_eq(v_n_3077_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__3));
v___x_3085_ = lean_string_dec_eq(v_n_3077_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3086_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__4));
v___x_3087_ = lean_string_dec_eq(v_n_3077_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3088_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__5));
v___x_3089_ = lean_string_dec_eq(v_n_3077_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___closed__6));
v___x_3091_ = lean_string_dec_eq(v_n_3077_, v___x_3090_);
lean_dec_ref(v_n_3077_);
return v___x_3091_;
}
else
{
lean_dec_ref(v_n_3077_);
return v___x_3089_;
}
}
else
{
lean_dec_ref(v_n_3077_);
return v___x_3087_;
}
}
else
{
lean_dec_ref(v_n_3077_);
return v___x_3085_;
}
}
else
{
lean_dec_ref(v_n_3077_);
return v___x_3083_;
}
}
else
{
lean_dec_ref(v_n_3077_);
return v___x_3081_;
}
}
else
{
lean_dec_ref(v_n_3077_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField___boxed(lean_object* v_name_3092_){
_start:
{
uint8_t v_res_3093_; lean_object* v_r_3094_; 
v_res_3093_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_name_3092_);
v_r_3094_ = lean_box(v_res_3093_);
return v_r_3094_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3100_){
_start:
{
lean_object* v___x_3101_; lean_object* v_n_3102_; uint8_t v___x_3103_; 
v___x_3101_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_name_3100_);
v_n_3102_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField_spec__0(v_name_3100_, v___x_3101_);
v___x_3103_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_name_3100_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3104_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3105_ = lean_string_dec_eq(v_n_3102_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3107_ = lean_string_dec_eq(v_n_3102_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3108_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3109_ = lean_string_dec_eq(v_n_3102_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3111_ = lean_string_dec_eq(v_n_3102_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3113_ = lean_string_dec_eq(v_n_3102_, v___x_3112_);
lean_dec_ref(v_n_3102_);
return v___x_3113_;
}
else
{
lean_dec_ref(v_n_3102_);
return v___x_3111_;
}
}
else
{
lean_dec_ref(v_n_3102_);
return v___x_3109_;
}
}
else
{
lean_dec_ref(v_n_3102_);
return v___x_3107_;
}
}
else
{
lean_dec_ref(v_n_3102_);
return v___x_3105_;
}
}
else
{
lean_dec_ref(v_n_3102_);
return v___x_3103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3114_){
_start:
{
uint8_t v_res_3115_; lean_object* v_r_3116_; 
v_res_3115_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3114_);
v_r_3116_ = lean_box(v_res_3115_);
return v_r_3116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3118_, uint8_t v_strict_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3118_, v_a_3120_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_res_3122_; 
v_res_3122_ = lean_ctor_get(v___x_3121_, 1);
lean_inc(v_res_3122_);
if (lean_obj_tag(v_res_3122_) == 1)
{
lean_object* v_val_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3145_; 
v_val_3123_ = lean_ctor_get(v_res_3122_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_res_3122_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3125_ = v_res_3122_;
v_isShared_3126_ = v_isSharedCheck_3145_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_val_3123_);
lean_dec(v_res_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3145_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v_pos_3127_; lean_object* v_fst_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3143_; 
v_pos_3127_ = lean_ctor_get(v___x_3121_, 0);
v_fst_3128_ = lean_ctor_get(v_val_3123_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_val_3123_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; 
v_unused_3144_ = lean_ctor_get(v_val_3123_, 1);
lean_dec(v_unused_3144_);
v___x_3130_ = v_val_3123_;
v_isShared_3131_ = v_isSharedCheck_3143_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_fst_3128_);
lean_dec(v_val_3123_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3143_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
uint8_t v___x_3141_; 
lean_inc(v_fst_3128_);
v___x_3141_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFramingTrailerField(v_fst_3128_);
if (v___x_3141_ == 0)
{
if (v_strict_3119_ == 0)
{
lean_del_object(v___x_3130_);
lean_dec(v_fst_3128_);
lean_del_object(v___x_3125_);
return v___x_3121_;
}
else
{
uint8_t v___x_3142_; 
lean_inc(v_fst_3128_);
v___x_3142_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3128_);
if (v___x_3142_ == 0)
{
lean_del_object(v___x_3130_);
lean_dec(v_fst_3128_);
lean_del_object(v___x_3125_);
return v___x_3121_;
}
else
{
lean_inc(v_pos_3127_);
lean_dec_ref_known(v___x_3121_, 2);
goto v___jp_3132_;
}
}
}
else
{
lean_inc(v_pos_3127_);
lean_dec_ref_known(v___x_3121_, 2);
goto v___jp_3132_;
}
v___jp_3132_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3133_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3134_ = lean_string_append(v___x_3133_, v_fst_3128_);
lean_dec(v_fst_3128_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3134_);
v___x_3136_ = v___x_3125_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 1);
lean_ctor_set(v___x_3130_, 1, v___x_3136_);
lean_ctor_set(v___x_3130_, 0, v_pos_3127_);
v___x_3138_ = v___x_3130_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_pos_3127_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3122_);
return v___x_3121_;
}
}
else
{
return v___x_3121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3146_, lean_object* v_strict_3147_, lean_object* v_a_3148_){
_start:
{
uint8_t v_strict_boxed_3149_; lean_object* v_res_3150_; 
v_strict_boxed_3149_ = lean_unbox(v_strict_3147_);
v_res_3150_ = l_Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3146_, v_strict_boxed_3149_, v_a_3148_);
lean_dec_ref(v_limits_3146_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_maxTrailerHeaders_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_maxTrailerHeaders_3153_ = lean_ctor_get(v_limits_3151_, 17);
lean_inc(v_maxTrailerHeaders_3153_);
v___x_3154_ = 1;
v___x_3155_ = lean_box(v___x_3154_);
v___x_3156_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseTrailerHeader___boxed), 3, 2);
lean_closure_set(v___x_3156_, 0, v_limits_3151_);
lean_closure_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3156_, v_maxTrailerHeaders_3153_, v_a_3152_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_pos_3158_; lean_object* v_res_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_pos_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_pos_3158_);
v_res_3159_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_res_3159_);
lean_dec_ref_known(v___x_3157_, 2);
v___x_3160_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3161_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3160_, v_pos_3158_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_pos_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_pos_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v___x_3161_, 1);
lean_dec(v_unused_3170_);
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_pos_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 1, v_res_3159_);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_pos_3162_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_res_3159_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v_pos_3171_; lean_object* v_err_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v_res_3159_);
v_pos_3171_ = lean_ctor_get(v___x_3161_, 0);
v_err_3172_ = lean_ctor_get(v___x_3161_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3161_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_err_3172_);
lean_inc(v_pos_3171_);
lean_dec(v___x_3161_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_pos_3171_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_err_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
return v___x_3157_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3180_){
_start:
{
uint32_t v___x_3181_; uint32_t v___x_3189_; uint8_t v___x_3190_; 
v___x_3181_ = lean_uint8_to_uint32(v_c_3180_);
v___x_3189_ = 33;
v___x_3190_ = lean_uint32_dec_le(v___x_3189_, v___x_3181_);
if (v___x_3190_ == 0)
{
goto v___jp_3182_;
}
else
{
uint32_t v___x_3191_; uint8_t v___x_3192_; 
v___x_3191_ = 126;
v___x_3192_ = lean_uint32_dec_le(v___x_3181_, v___x_3191_);
if (v___x_3192_ == 0)
{
goto v___jp_3182_;
}
else
{
return v___x_3192_;
}
}
v___jp_3182_:
{
uint32_t v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = 128;
v___x_3184_ = lean_uint32_dec_le(v___x_3183_, v___x_3181_);
if (v___x_3184_ == 0)
{
uint32_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = 32;
v___x_3186_ = lean_uint32_dec_eq(v___x_3181_, v___x_3185_);
if (v___x_3186_ == 0)
{
uint32_t v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = 9;
v___x_3188_ = lean_uint32_dec_eq(v___x_3181_, v___x_3187_);
return v___x_3188_;
}
else
{
return v___x_3186_;
}
}
else
{
return v___x_3184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3193_){
_start:
{
uint8_t v_c_boxed_3194_; uint8_t v_res_3195_; lean_object* v_r_3196_; 
v_c_boxed_3194_ = lean_unbox(v_c_3193_);
v_res_3195_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3194_);
v_r_3196_ = lean_box(v_res_3195_);
return v_r_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_maxReasonPhraseLength_3199_; lean_object* v___f_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_snd_3203_; lean_object* v_snd_3204_; uint8_t v___x_3205_; 
v_maxReasonPhraseLength_3199_ = lean_ctor_get(v_limits_3197_, 16);
v___f_3200_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_3201_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3198_);
v___x_3202_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3200_, v_maxReasonPhraseLength_3199_, v___x_3201_, v_a_3198_);
v_snd_3203_ = lean_ctor_get(v___x_3202_, 1);
lean_inc(v_snd_3203_);
v_snd_3204_ = lean_ctor_get(v_snd_3203_, 1);
v___x_3205_ = lean_unbox(v_snd_3204_);
if (v___x_3205_ == 0)
{
lean_object* v_fst_3206_; lean_object* v_fst_3207_; lean_object* v_array_3208_; lean_object* v_idx_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3229_; 
v_fst_3206_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_fst_3206_);
lean_dec_ref(v___x_3202_);
v_fst_3207_ = lean_ctor_get(v_snd_3203_, 0);
lean_inc(v_fst_3207_);
lean_dec(v_snd_3203_);
v_array_3208_ = lean_ctor_get(v_a_3198_, 0);
v_idx_3209_ = lean_ctor_get(v_a_3198_, 1);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_a_3198_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3211_ = v_a_3198_;
v_isShared_3212_ = v_isSharedCheck_3229_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_idx_3209_);
lean_inc(v_array_3208_);
lean_dec(v_a_3198_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3229_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_lower_3214_; lean_object* v_upper_3215_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___y_3226_; uint8_t v___x_3228_; 
v___x_3223_ = lean_nat_add(v_idx_3209_, v_fst_3206_);
lean_dec(v_fst_3206_);
v___x_3224_ = lean_byte_array_size(v_array_3208_);
v___x_3228_ = lean_nat_dec_le(v_idx_3209_, v___x_3201_);
if (v___x_3228_ == 0)
{
v___y_3226_ = v_idx_3209_;
goto v___jp_3225_;
}
else
{
lean_dec(v_idx_3209_);
v___y_3226_ = v___x_3201_;
goto v___jp_3225_;
}
v___jp_3213_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3216_ = l_ByteArray_toByteSlice(v_array_3208_, v_lower_3214_, v_upper_3215_);
v___x_3217_ = l_ByteSlice_toByteArray(v___x_3216_);
v___x_3218_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_3219_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v___x_3217_, v___x_3201_, v___x_3218_);
lean_dec_ref(v___x_3217_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v___x_3219_);
lean_ctor_set(v___x_3211_, 0, v_fst_3207_);
v___x_3221_ = v___x_3211_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_fst_3207_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
v___jp_3225_:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_nat_dec_le(v___x_3223_, v___x_3224_);
if (v___x_3227_ == 0)
{
lean_dec(v___x_3223_);
v_lower_3214_ = v___y_3226_;
v_upper_3215_ = v___x_3224_;
goto v___jp_3213_;
}
else
{
v_lower_3214_ = v___y_3226_;
v_upper_3215_ = v___x_3223_;
goto v___jp_3213_;
}
}
}
}
else
{
lean_object* v_fst_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3238_; 
lean_dec_ref(v___x_3202_);
lean_dec_ref(v_a_3198_);
v_fst_3230_ = lean_ctor_get(v_snd_3203_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_snd_3203_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v_snd_3203_, 1);
lean_dec(v_unused_3239_);
v___x_3232_ = v_snd_3203_;
v_isShared_3233_ = v_isSharedCheck_3238_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_fst_3230_);
lean_dec(v_snd_3203_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3238_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = lean_box(0);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 1);
lean_ctor_set(v___x_3232_, 1, v___x_3234_);
v___x_3236_ = v___x_3232_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_fst_3230_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3240_, v_a_3241_);
lean_dec_ref(v_limits_3240_);
return v_res_3242_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3243_){
_start:
{
if (lean_obj_tag(v_x_3243_) == 0)
{
uint8_t v___x_3244_; 
v___x_3244_ = 1;
return v___x_3244_;
}
else
{
lean_object* v_head_3245_; lean_object* v_tail_3246_; uint32_t v___x_3252_; uint32_t v___x_3253_; uint8_t v___x_3254_; 
v_head_3245_ = lean_ctor_get(v_x_3243_, 0);
v_tail_3246_ = lean_ctor_get(v_x_3243_, 1);
v___x_3252_ = 9;
v___x_3253_ = lean_unbox_uint32(v_head_3245_);
v___x_3254_ = lean_uint32_dec_eq(v___x_3253_, v___x_3252_);
if (v___x_3254_ == 0)
{
uint32_t v___x_3255_; uint32_t v___x_3256_; uint8_t v___x_3257_; 
v___x_3255_ = 32;
v___x_3256_ = lean_unbox_uint32(v_head_3245_);
v___x_3257_ = lean_uint32_dec_eq(v___x_3256_, v___x_3255_);
if (v___x_3257_ == 0)
{
uint32_t v___x_3258_; uint32_t v___x_3259_; uint8_t v___x_3260_; 
v___x_3258_ = 33;
v___x_3259_ = lean_unbox_uint32(v_head_3245_);
v___x_3260_ = lean_uint32_dec_le(v___x_3258_, v___x_3259_);
if (v___x_3260_ == 0)
{
goto v___jp_3247_;
}
else
{
uint32_t v___x_3261_; uint32_t v___x_3262_; uint8_t v___x_3263_; 
v___x_3261_ = 126;
v___x_3262_ = lean_unbox_uint32(v_head_3245_);
v___x_3263_ = lean_uint32_dec_le(v___x_3262_, v___x_3261_);
if (v___x_3263_ == 0)
{
goto v___jp_3247_;
}
else
{
v_x_3243_ = v_tail_3246_;
goto _start;
}
}
}
else
{
v_x_3243_ = v_tail_3246_;
goto _start;
}
}
else
{
v_x_3243_ = v_tail_3246_;
goto _start;
}
v___jp_3247_:
{
uint32_t v___x_3248_; uint32_t v___x_3249_; uint8_t v___x_3250_; 
v___x_3248_ = 128;
v___x_3249_ = lean_unbox_uint32(v_head_3245_);
v___x_3250_ = lean_uint32_dec_le(v___x_3248_, v___x_3249_);
if (v___x_3250_ == 0)
{
return v___x_3250_;
}
else
{
v_x_3243_ = v_tail_3246_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3267_){
_start:
{
uint8_t v_res_3268_; lean_object* v_r_3269_; 
v_res_3268_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3267_);
lean_dec(v_x_3267_);
v_r_3269_ = lean_box(v_res_3268_);
return v_r_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v___y_3279_; lean_object* v_array_3282_; lean_object* v_idx_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_array_3282_ = lean_ctor_get(v_a_3274_, 0);
v_idx_3283_ = lean_ctor_get(v_a_3274_, 1);
v___x_3284_ = lean_byte_array_size(v_array_3282_);
v___x_3285_ = lean_nat_dec_lt(v_idx_3283_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = lean_box(0);
v___x_3287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_a_3274_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
return v___x_3287_;
}
else
{
uint8_t v_c_3288_; uint8_t v___x_3289_; uint8_t v___x_3290_; 
v_c_3288_ = lean_byte_array_fget(v_array_3282_, v_idx_3283_);
v___x_3289_ = 48;
v___x_3290_ = lean_uint8_dec_le(v___x_3289_, v_c_3288_);
if (v___x_3290_ == 0)
{
goto v___jp_3275_;
}
else
{
uint8_t v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = 57;
v___x_3292_ = lean_uint8_dec_le(v_c_3288_, v___x_3291_);
if (v___x_3292_ == 0)
{
goto v___jp_3275_;
}
else
{
lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3389_; 
lean_inc(v_idx_3283_);
lean_inc_ref(v_array_3282_);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_a_3274_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; lean_object* v_unused_3391_; 
v_unused_3390_ = lean_ctor_get(v_a_3274_, 1);
lean_dec(v_unused_3390_);
v_unused_3391_ = lean_ctor_get(v_a_3274_, 0);
lean_dec(v_unused_3391_);
v___x_3294_ = v_a_3274_;
v_isShared_3295_ = v_isSharedCheck_3389_;
goto v_resetjp_3293_;
}
else
{
lean_dec(v_a_3274_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3389_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v_it_x27_3299_; 
v___x_3296_ = lean_unsigned_to_nat(1u);
v___x_3297_ = lean_nat_add(v_idx_3283_, v___x_3296_);
lean_dec(v_idx_3283_);
lean_inc(v___x_3297_);
lean_inc_ref(v_array_3282_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 1, v___x_3297_);
v_it_x27_3299_ = v___x_3294_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_array_3282_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v___x_3297_);
v_it_x27_3299_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
uint8_t v___x_3303_; 
v___x_3303_ = lean_nat_dec_lt(v___x_3297_, v___x_3284_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec(v___x_3297_);
lean_dec_ref(v_array_3282_);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3305_, 0, v_it_x27_3299_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
return v___x_3305_;
}
else
{
uint8_t v_c_3306_; uint8_t v___x_3307_; 
v_c_3306_ = lean_byte_array_fget(v_array_3282_, v___x_3297_);
v___x_3307_ = lean_uint8_dec_le(v___x_3289_, v_c_3306_);
if (v___x_3307_ == 0)
{
lean_dec(v___x_3297_);
lean_dec_ref(v_array_3282_);
goto v___jp_3300_;
}
else
{
uint8_t v___x_3308_; 
v___x_3308_ = lean_uint8_dec_le(v_c_3306_, v___x_3291_);
if (v___x_3308_ == 0)
{
lean_dec(v___x_3297_);
lean_dec_ref(v_array_3282_);
goto v___jp_3300_;
}
else
{
lean_object* v___x_3309_; lean_object* v_it_x27_3310_; uint8_t v___x_3314_; 
lean_dec_ref(v_it_x27_3299_);
v___x_3309_ = lean_nat_add(v___x_3297_, v___x_3296_);
lean_dec(v___x_3297_);
lean_inc(v___x_3309_);
lean_inc_ref(v_array_3282_);
v_it_x27_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3310_, 0, v_array_3282_);
lean_ctor_set(v_it_x27_3310_, 1, v___x_3309_);
v___x_3314_ = lean_nat_dec_lt(v___x_3309_, v___x_3284_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec(v___x_3309_);
lean_dec_ref(v_array_3282_);
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3316_, 0, v_it_x27_3310_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
return v___x_3316_;
}
else
{
uint8_t v_c_3317_; uint8_t v___x_3318_; 
v_c_3317_ = lean_byte_array_fget(v_array_3282_, v___x_3309_);
v___x_3318_ = lean_uint8_dec_le(v___x_3289_, v_c_3317_);
if (v___x_3318_ == 0)
{
lean_dec(v___x_3309_);
lean_dec_ref(v_array_3282_);
goto v___jp_3311_;
}
else
{
uint8_t v___x_3319_; 
v___x_3319_ = lean_uint8_dec_le(v_c_3317_, v___x_3291_);
if (v___x_3319_ == 0)
{
lean_dec(v___x_3309_);
lean_dec_ref(v_array_3282_);
goto v___jp_3311_;
}
else
{
lean_object* v___x_3320_; uint32_t v___x_3321_; uint32_t v___x_3322_; lean_object* v___x_3323_; lean_object* v_it_x27_3324_; uint32_t v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v_pos_3368_; lean_object* v_idx_3369_; lean_object* v_err_3370_; uint8_t v___x_3374_; 
lean_dec_ref_known(v_it_x27_3310_, 2);
v___x_3320_ = lean_unsigned_to_nat(48u);
v___x_3321_ = lean_uint8_to_uint32(v_c_3288_);
v___x_3322_ = lean_uint8_to_uint32(v_c_3306_);
v___x_3323_ = lean_nat_add(v___x_3309_, v___x_3296_);
lean_dec(v___x_3309_);
lean_inc(v___x_3323_);
lean_inc_ref(v_array_3282_);
v_it_x27_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3324_, 0, v_array_3282_);
lean_ctor_set(v_it_x27_3324_, 1, v___x_3323_);
v___x_3325_ = lean_uint8_to_uint32(v_c_3317_);
v___x_3326_ = lean_uint32_to_nat(v___x_3321_);
v___x_3327_ = lean_nat_sub(v___x_3326_, v___x_3320_);
lean_dec(v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(100u);
v___x_3329_ = lean_nat_mul(v___x_3327_, v___x_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_uint32_to_nat(v___x_3322_);
v___x_3331_ = lean_nat_sub(v___x_3330_, v___x_3320_);
lean_dec(v___x_3330_);
v___x_3332_ = lean_unsigned_to_nat(10u);
v___x_3333_ = lean_nat_mul(v___x_3331_, v___x_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_nat_add(v___x_3329_, v___x_3333_);
lean_dec(v___x_3333_);
lean_dec(v___x_3329_);
v___x_3335_ = lean_uint32_to_nat(v___x_3325_);
v___x_3336_ = lean_nat_sub(v___x_3335_, v___x_3320_);
lean_dec(v___x_3335_);
v___x_3337_ = lean_nat_add(v___x_3334_, v___x_3336_);
lean_dec(v___x_3336_);
lean_dec(v___x_3334_);
v___x_3374_ = lean_nat_dec_lt(v___x_3323_, v___x_3284_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; 
lean_dec_ref(v_array_3282_);
v___x_3375_ = lean_box(0);
lean_inc(v___x_3323_);
v_pos_3368_ = v_it_x27_3324_;
v_idx_3369_ = v___x_3323_;
v_err_3370_ = v___x_3375_;
goto v___jp_3367_;
}
else
{
uint8_t v___x_3376_; uint8_t v_got_3377_; uint8_t v___x_3378_; 
v___x_3376_ = 32;
v_got_3377_ = lean_byte_array_fget(v_array_3282_, v___x_3323_);
v___x_3378_ = lean_uint8_dec_eq(v_got_3377_, v___x_3376_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
lean_dec_ref(v_array_3282_);
v___x_3379_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
lean_inc(v___x_3323_);
v_pos_3368_ = v_it_x27_3324_;
v_idx_3369_ = v___x_3323_;
v_err_3370_ = v___x_3379_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_dec_ref_known(v_it_x27_3324_, 2);
v___x_3380_ = lean_nat_add(v___x_3323_, v___x_3296_);
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v_array_3282_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3273_, v___x_3381_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_pos_3383_; lean_object* v_res_3384_; 
lean_dec(v___x_3323_);
v_pos_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_pos_3383_);
v_res_3384_ = lean_ctor_get(v___x_3382_, 1);
lean_inc(v_res_3384_);
lean_dec_ref_known(v___x_3382_, 2);
v___y_3339_ = v_pos_3383_;
v___y_3340_ = v_res_3384_;
goto v___jp_3338_;
}
else
{
lean_object* v_pos_3385_; lean_object* v___x_3386_; lean_object* v_idx_3387_; 
v_pos_3385_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_pos_3385_);
lean_dec_ref_known(v___x_3382_, 2);
v___x_3386_ = lean_box(0);
v_idx_3387_ = lean_ctor_get(v_pos_3385_, 1);
lean_inc(v_idx_3387_);
v_pos_3368_ = v_pos_3385_;
v_idx_3369_ = v_idx_3387_;
v_err_3370_ = v___x_3386_;
goto v___jp_3367_;
}
}
}
v___jp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3342_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3341_, v___y_3339_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_pos_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3356_; 
v_pos_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v___x_3342_, 1);
lean_dec(v_unused_3357_);
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3356_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_pos_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3356_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; uint8_t v___x_3348_; 
lean_inc_ref(v___y_3340_);
v___x_3347_ = l_String_toListImpl(v___y_3340_);
v___x_3348_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3347_);
lean_dec(v___x_3347_);
if (v___x_3348_ == 0)
{
lean_del_object(v___x_3345_);
lean_dec_ref(v___y_3340_);
lean_dec(v___x_3337_);
v___y_3279_ = v_pos_3343_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3349_; uint16_t v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___y_3340_);
v___x_3350_ = lean_uint16_of_nat(v___x_3337_);
lean_dec(v___x_3337_);
v___x_3351_ = l_Std_Http_Status_ofCode(v___x_3349_, v___x_3350_);
if (lean_obj_tag(v___x_3351_) == 1)
{
lean_object* v_val_3352_; lean_object* v___x_3354_; 
v_val_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_val_3352_);
lean_dec_ref_known(v___x_3351_, 1);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v_val_3352_);
v___x_3354_ = v___x_3345_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_pos_3343_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_val_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
else
{
lean_dec(v___x_3351_);
lean_del_object(v___x_3345_);
v___y_3279_ = v_pos_3343_;
goto v___jp_3278_;
}
}
}
}
else
{
lean_object* v_pos_3358_; lean_object* v_err_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec_ref(v___y_3340_);
lean_dec(v___x_3337_);
v_pos_3358_ = lean_ctor_get(v___x_3342_, 0);
v_err_3359_ = lean_ctor_get(v___x_3342_, 1);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3342_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_err_3359_);
lean_inc(v_pos_3358_);
lean_dec(v___x_3342_);
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
v___jp_3367_:
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_nat_dec_eq(v___x_3323_, v_idx_3369_);
lean_dec(v_idx_3369_);
lean_dec(v___x_3323_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; 
lean_dec(v___x_3337_);
lean_inc(v_err_3370_);
v___x_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3372_, 0, v_pos_3368_);
lean_ctor_set(v___x_3372_, 1, v_err_3370_);
return v___x_3372_;
}
else
{
lean_object* v___x_3373_; 
v___x_3373_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___y_3339_ = v_pos_3368_;
v___y_3340_ = v___x_3373_;
goto v___jp_3338_;
}
}
}
}
}
v___jp_3311_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_it_x27_3310_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
return v___x_3313_;
}
}
}
}
v___jp_3300_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_it_x27_3299_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
return v___x_3302_;
}
}
}
}
}
}
v___jp_3275_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3277_, 0, v_a_3274_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
return v___x_3277_;
}
v___jp_3278_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_3281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___y_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3392_, v_a_3393_);
lean_dec_ref(v_limits_3392_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3396_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_pos_3398_; lean_object* v_res_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3473_; 
v_pos_3398_ = lean_ctor_get(v___x_3397_, 0);
v_res_3399_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3401_ = v___x_3397_;
v_isShared_3402_ = v_isSharedCheck_3473_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_res_3399_);
lean_inc(v_pos_3398_);
lean_dec(v___x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3473_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_array_3403_; lean_object* v_idx_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v_array_3403_ = lean_ctor_get(v_pos_3398_, 0);
v_idx_3404_ = lean_ctor_get(v_pos_3398_, 1);
v___x_3405_ = lean_byte_array_size(v_array_3403_);
v___x_3406_ = lean_nat_dec_lt(v_idx_3404_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3409_; 
lean_dec(v_res_3399_);
v___x_3407_ = lean_box(0);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 1, v___x_3407_);
v___x_3409_ = v___x_3401_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_pos_3398_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
else
{
uint8_t v___x_3411_; uint8_t v_got_3412_; uint8_t v___x_3413_; 
v___x_3411_ = 32;
v_got_3412_ = lean_byte_array_fget(v_array_3403_, v_idx_3404_);
v___x_3413_ = lean_uint8_dec_eq(v_got_3412_, v___x_3411_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec(v_res_3399_);
v___x_3414_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 1, v___x_3414_);
v___x_3416_ = v___x_3401_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_pos_3398_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
else
{
lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3470_; 
lean_inc(v_idx_3404_);
lean_inc_ref(v_array_3403_);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_pos_3398_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; lean_object* v_unused_3472_; 
v_unused_3471_ = lean_ctor_get(v_pos_3398_, 1);
lean_dec(v_unused_3471_);
v_unused_3472_ = lean_ctor_get(v_pos_3398_, 0);
lean_dec(v_unused_3472_);
v___x_3419_ = v_pos_3398_;
v_isShared_3420_ = v_isSharedCheck_3470_;
goto v_resetjp_3418_;
}
else
{
lean_dec(v_pos_3398_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3470_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v_fst_3421_; lean_object* v_snd_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3469_; 
v_fst_3421_ = lean_ctor_get(v_res_3399_, 0);
v_snd_3422_ = lean_ctor_get(v_res_3399_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_res_3399_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3424_ = v_res_3399_;
v_isShared_3425_ = v_isSharedCheck_3469_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_snd_3422_);
lean_inc(v_fst_3421_);
lean_dec(v_res_3399_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3469_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3426_ = lean_unsigned_to_nat(1u);
v___x_3427_ = lean_nat_add(v_idx_3404_, v___x_3426_);
lean_dec(v_idx_3404_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 1, v___x_3427_);
v___x_3429_ = v___x_3419_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_array_3403_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3430_; 
v___x_3430_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3395_, v___x_3429_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_pos_3431_; lean_object* v_res_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3458_; 
v_pos_3431_ = lean_ctor_get(v___x_3430_, 0);
v_res_3432_ = lean_ctor_get(v___x_3430_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3434_ = v___x_3430_;
v_isShared_3435_ = v_isSharedCheck_3458_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_res_3432_);
lean_inc(v_pos_3431_);
lean_dec(v___x_3430_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3458_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_nat_dec_eq(v_fst_3421_, v___x_3426_);
lean_dec(v_fst_3421_);
if (v___x_3441_ == 0)
{
lean_del_object(v___x_3424_);
goto v___jp_3442_;
}
else
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_nat_dec_le(v___x_3426_, v_snd_3422_);
if (v___x_3451_ == 0)
{
lean_del_object(v___x_3424_);
goto v___jp_3442_;
}
else
{
uint8_t v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
lean_del_object(v___x_3434_);
lean_dec(v_snd_3422_);
lean_del_object(v___x_3401_);
v___x_3452_ = 1;
v___x_3453_ = l_Std_Http_Headers_empty;
v___x_3454_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3454_, 0, v_res_3432_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
lean_ctor_set_uint8(v___x_3454_, sizeof(void*)*2, v___x_3452_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 1, v___x_3454_);
lean_ctor_set(v___x_3424_, 0, v_pos_3431_);
v___x_3456_ = v___x_3424_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_pos_3431_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
v___jp_3436_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 1, v___x_3437_);
v___x_3439_ = v___x_3434_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_pos_3431_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
v___jp_3442_:
{
if (v___x_3441_ == 0)
{
lean_dec(v_res_3432_);
lean_dec(v_snd_3422_);
lean_del_object(v___x_3401_);
goto v___jp_3436_;
}
else
{
lean_object* v___x_3443_; uint8_t v___x_3444_; 
v___x_3443_ = lean_unsigned_to_nat(0u);
v___x_3444_ = lean_nat_dec_eq(v_snd_3422_, v___x_3443_);
lean_dec(v_snd_3422_);
if (v___x_3444_ == 0)
{
lean_dec(v_res_3432_);
lean_del_object(v___x_3401_);
goto v___jp_3436_;
}
else
{
uint8_t v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_del_object(v___x_3434_);
v___x_3445_ = 0;
v___x_3446_ = l_Std_Http_Headers_empty;
v___x_3447_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3447_, 0, v_res_3432_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
lean_ctor_set_uint8(v___x_3447_, sizeof(void*)*2, v___x_3445_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3447_);
lean_ctor_set(v___x_3401_, 0, v_pos_3431_);
v___x_3449_ = v___x_3401_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_pos_3431_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3459_; lean_object* v_err_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_del_object(v___x_3424_);
lean_dec(v_snd_3422_);
lean_dec(v_fst_3421_);
lean_del_object(v___x_3401_);
v_pos_3459_ = lean_ctor_get(v___x_3430_, 0);
v_err_3460_ = lean_ctor_get(v___x_3430_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3430_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_err_3460_);
lean_inc(v_pos_3459_);
lean_dec(v___x_3430_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_pos_3459_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_err_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
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
lean_object* v_pos_3474_; lean_object* v_err_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_pos_3474_ = lean_ctor_get(v___x_3397_, 0);
v_err_3475_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3397_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_err_3475_);
lean_inc(v_pos_3474_);
lean_dec(v___x_3397_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_pos_3474_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_err_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_3483_, v_a_3484_);
lean_dec_ref(v_limits_3483_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3487_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_pos_3489_; lean_object* v_res_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3553_; 
v_pos_3489_ = lean_ctor_get(v___x_3488_, 0);
v_res_3490_ = lean_ctor_get(v___x_3488_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3492_ = v___x_3488_;
v_isShared_3493_ = v_isSharedCheck_3553_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_res_3490_);
lean_inc(v_pos_3489_);
lean_dec(v___x_3488_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3553_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_array_3494_; lean_object* v_idx_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v_array_3494_ = lean_ctor_get(v_pos_3489_, 0);
v_idx_3495_ = lean_ctor_get(v_pos_3489_, 1);
v___x_3496_ = lean_byte_array_size(v_array_3494_);
v___x_3497_ = lean_nat_dec_lt(v_idx_3495_, v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
lean_dec(v_res_3490_);
v___x_3498_ = lean_box(0);
if (v_isShared_3493_ == 0)
{
lean_ctor_set_tag(v___x_3492_, 1);
lean_ctor_set(v___x_3492_, 1, v___x_3498_);
v___x_3500_ = v___x_3492_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_pos_3489_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
else
{
uint8_t v___x_3502_; uint8_t v_got_3503_; uint8_t v___x_3504_; 
v___x_3502_ = 32;
v_got_3503_ = lean_byte_array_fget(v_array_3494_, v_idx_3495_);
v___x_3504_ = lean_uint8_dec_eq(v_got_3503_, v___x_3502_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
lean_dec(v_res_3490_);
v___x_3505_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_3493_ == 0)
{
lean_ctor_set_tag(v___x_3492_, 1);
lean_ctor_set(v___x_3492_, 1, v___x_3505_);
v___x_3507_ = v___x_3492_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_pos_3489_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
else
{
lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3550_; 
lean_inc(v_idx_3495_);
lean_inc_ref(v_array_3494_);
lean_del_object(v___x_3492_);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_pos_3489_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; lean_object* v_unused_3552_; 
v_unused_3551_ = lean_ctor_get(v_pos_3489_, 1);
lean_dec(v_unused_3551_);
v_unused_3552_ = lean_ctor_get(v_pos_3489_, 0);
lean_dec(v_unused_3552_);
v___x_3510_ = v_pos_3489_;
v_isShared_3511_ = v_isSharedCheck_3550_;
goto v_resetjp_3509_;
}
else
{
lean_dec(v_pos_3489_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3550_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_fst_3512_; lean_object* v_snd_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3549_; 
v_fst_3512_ = lean_ctor_get(v_res_3490_, 0);
v_snd_3513_ = lean_ctor_get(v_res_3490_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_res_3490_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3515_ = v_res_3490_;
v_isShared_3516_ = v_isSharedCheck_3549_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_snd_3513_);
lean_inc(v_fst_3512_);
lean_dec(v_res_3490_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3549_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_nat_add(v_idx_3495_, v___x_3517_);
lean_dec(v_idx_3495_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3518_);
v___x_3520_ = v___x_3510_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_array_3494_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; 
v___x_3521_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3486_, v___x_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_pos_3522_; lean_object* v_res_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3538_; 
v_pos_3522_ = lean_ctor_get(v___x_3521_, 0);
v_res_3523_ = lean_ctor_get(v___x_3521_, 1);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3525_ = v___x_3521_;
v_isShared_3526_ = v_isSharedCheck_3538_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_res_3523_);
lean_inc(v_pos_3522_);
lean_dec(v___x_3521_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3538_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___y_3528_; uint8_t v___x_3536_; 
v___x_3536_ = lean_nat_dec_eq(v_fst_3512_, v___x_3517_);
if (v___x_3536_ == 0)
{
v___y_3528_ = v_snd_3513_;
goto v___jp_3527_;
}
else
{
uint8_t v___x_3537_; 
v___x_3537_ = lean_nat_dec_le(v_snd_3513_, v___x_3517_);
if (v___x_3537_ == 0)
{
lean_dec(v_snd_3513_);
v___y_3528_ = v___x_3517_;
goto v___jp_3527_;
}
else
{
v___y_3528_ = v_snd_3513_;
goto v___jp_3527_;
}
}
v___jp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = l_Std_Http_Version_ofNumber_x3f(v_fst_3512_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec(v_fst_3512_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v___x_3529_);
lean_ctor_set(v___x_3515_, 0, v_res_3523_);
v___x_3531_ = v___x_3515_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_res_3523_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3533_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 1, v___x_3531_);
v___x_3533_ = v___x_3525_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_pos_3522_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3531_);
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
else
{
lean_object* v_pos_3539_; lean_object* v_err_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_del_object(v___x_3515_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
v_pos_3539_ = lean_ctor_get(v___x_3521_, 0);
v_err_3540_ = lean_ctor_get(v___x_3521_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3521_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_err_3540_);
lean_inc(v_pos_3539_);
lean_dec(v___x_3521_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_pos_3539_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_err_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
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
lean_object* v_pos_3554_; lean_object* v_err_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_pos_3554_ = lean_ctor_get(v___x_3488_, 0);
v_err_3555_ = lean_ctor_get(v___x_3488_, 1);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3488_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_err_3555_);
lean_inc(v_pos_3554_);
lean_dec(v___x_3488_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_pos_3554_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_err_3555_);
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
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_3563_, v_a_3564_);
lean_dec_ref(v_limits_3563_);
return v_res_3565_;
}
}
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lossy(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Lossy(builtin);
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
lean_object* initialize_Init_Data_String_Lossy(uint8_t builtin);
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
res = initialize_Init_Data_String_Lossy(builtin);
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
