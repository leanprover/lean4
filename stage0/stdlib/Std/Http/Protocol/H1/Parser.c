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
extern lean_object* l_Std_Http_Headers_empty;
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_String_toListImpl(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* l_Std_Http_Status_ofCode(lean_object*, uint16_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
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
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(uint8_t v_c_1_){
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
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1_ = stack[0].m_num;
uint8_t v_res_12_;
v_res_12_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isFieldVChar(v_c_1_);
stack->m_num = v_res_12_;
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
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(uint8_t v_c_17_){
_start:
{
uint32_t v___x_18_; uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_18_ = lean_uint8_to_uint32(v_c_17_);
v___x_24_ = 9;
v___x_25_ = lean_uint32_dec_eq(v___x_18_, v___x_24_);
if (v___x_25_ == 0)
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 32;
v___x_27_ = lean_uint32_dec_eq(v___x_18_, v___x_26_);
if (v___x_27_ == 0)
{
uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 33;
v___x_29_ = lean_uint32_dec_eq(v___x_18_, v___x_28_);
if (v___x_29_ == 0)
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 35;
v___x_31_ = lean_uint32_dec_le(v___x_30_, v___x_18_);
if (v___x_31_ == 0)
{
goto v___jp_19_;
}
else
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 91;
v___x_33_ = lean_uint32_dec_le(v___x_18_, v___x_32_);
if (v___x_33_ == 0)
{
goto v___jp_19_;
}
else
{
return v___x_33_;
}
}
}
else
{
return v___x_29_;
}
}
else
{
return v___x_27_;
}
}
else
{
return v___x_25_;
}
v___jp_19_:
{
uint32_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 93;
v___x_21_ = lean_uint32_dec_le(v___x_20_, v___x_18_);
if (v___x_21_ == 0)
{
return v___x_21_;
}
else
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 126;
v___x_23_ = lean_uint32_dec_le(v___x_18_, v___x_22_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_17_ = stack[0].m_num;
uint8_t v_res_34_;
v_res_34_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isQdText(v_c_17_);
stack->m_num = v_res_34_;
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
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(uint8_t v_c_39_){
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
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_39_ = stack[0].m_num;
uint8_t v_res_45_;
v_res_45_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(v_c_39_);
stack->m_num = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte___boxed(lean_object* v_c_46_){
_start:
{
uint8_t v_c_boxed_47_; uint8_t v_res_48_; lean_object* v_r_49_; 
v_c_boxed_47_ = lean_unbox(v_c_46_);
v_res_48_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isOwsByte(v_c_boxed_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(lean_object* v_parser_55_, lean_object* v_maxCount_56_, lean_object* v_acc_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_pos_60_; lean_object* v_err_61_; lean_object* v___x_76_; 
lean_inc_ref(v_parser_55_);
lean_inc_ref(v_a_58_);
v___x_76_ = lean_apply_1(v_parser_55_, v_a_58_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_res_77_; 
v_res_77_ = lean_ctor_get(v___x_76_, 1);
lean_inc(v_res_77_);
if (lean_obj_tag(v_res_77_) == 0)
{
lean_object* v___x_78_; 
lean_dec_ref_known(v___x_76_, 2);
lean_dec(v_maxCount_56_);
lean_dec_ref(v_parser_55_);
v___x_78_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__1));
lean_inc_ref(v_a_58_);
v_pos_60_ = v_a_58_;
v_err_61_ = v___x_78_;
goto v___jp_59_;
}
else
{
lean_object* v_pos_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_105_; 
lean_dec_ref(v_a_58_);
v_pos_79_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_105_ == 0)
{
lean_object* v_unused_106_; 
v_unused_106_ = lean_ctor_get(v___x_76_, 1);
lean_dec(v_unused_106_);
v___x_81_ = v___x_76_;
v_isShared_82_ = v_isSharedCheck_105_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_pos_79_);
lean_dec(v___x_76_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_105_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v_val_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_104_; 
v_val_83_ = lean_ctor_get(v_res_77_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v_res_77_);
if (v_isSharedCheck_104_ == 0)
{
v___x_85_ = v_res_77_;
v_isShared_86_ = v_isSharedCheck_104_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_val_83_);
lean_dec(v_res_77_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_104_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_87_ = lean_array_push(v_acc_57_, v_val_83_);
v___x_88_ = lean_array_get_size(v___x_87_);
v___x_89_ = lean_nat_dec_lt(v_maxCount_56_, v___x_88_);
if (v___x_89_ == 0)
{
lean_del_object(v___x_85_);
lean_del_object(v___x_81_);
v_acc_57_ = v___x_87_;
v_a_58_ = v_pos_79_;
goto _start;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
lean_dec_ref(v___x_87_);
lean_dec_ref(v_parser_55_);
v___x_91_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__2));
v___x_92_ = l_Nat_reprFast(v___x_88_);
v___x_93_ = lean_string_append(v___x_91_, v___x_92_);
lean_dec_ref(v___x_92_);
v___x_94_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg___closed__3));
v___x_95_ = lean_string_append(v___x_93_, v___x_94_);
v___x_96_ = l_Nat_reprFast(v_maxCount_56_);
v___x_97_ = lean_string_append(v___x_95_, v___x_96_);
lean_dec_ref(v___x_96_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_97_);
v___x_99_ = v___x_85_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set_tag(v___x_81_, 1);
lean_ctor_set(v___x_81_, 1, v___x_99_);
v___x_101_ = v___x_81_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_pos_79_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
}
}
else
{
lean_object* v_err_107_; 
lean_dec(v_maxCount_56_);
lean_dec_ref(v_parser_55_);
v_err_107_ = lean_ctor_get(v___x_76_, 1);
lean_inc(v_err_107_);
lean_dec_ref_known(v___x_76_, 2);
lean_inc_ref(v_a_58_);
v_pos_60_ = v_a_58_;
v_err_61_ = v_err_107_;
goto v___jp_59_;
}
v___jp_59_:
{
lean_object* v_idx_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_74_; 
v_idx_62_ = lean_ctor_get(v_a_58_, 1);
v_isSharedCheck_74_ = !lean_is_exclusive(v_a_58_);
if (v_isSharedCheck_74_ == 0)
{
lean_object* v_unused_75_; 
v_unused_75_ = lean_ctor_get(v_a_58_, 0);
lean_dec(v_unused_75_);
v___x_64_ = v_a_58_;
v_isShared_65_ = v_isSharedCheck_74_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_idx_62_);
lean_dec(v_a_58_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_74_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v_idx_66_; uint8_t v___x_67_; 
v_idx_66_ = lean_ctor_get(v_pos_60_, 1);
v___x_67_ = lean_nat_dec_eq(v_idx_62_, v_idx_66_);
lean_dec(v_idx_62_);
if (v___x_67_ == 0)
{
lean_object* v___x_69_; 
lean_dec_ref(v_acc_57_);
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 1);
lean_ctor_set(v___x_64_, 1, v_err_61_);
lean_ctor_set(v___x_64_, 0, v_pos_60_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_pos_60_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_err_61_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
else
{
lean_object* v___x_72_; 
lean_dec(v_err_61_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v_acc_57_);
lean_ctor_set(v___x_64_, 0, v_pos_60_);
v___x_72_ = v___x_64_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_pos_60_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_acc_57_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go(lean_object* v_00_u03b1_108_, lean_object* v_parser_109_, lean_object* v_maxCount_110_, lean_object* v_acc_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_109_, v_maxCount_110_, v_acc_111_, v_a_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(lean_object* v_parser_116_, lean_object* v_maxCount_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg___closed__0));
v___x_120_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems_go___redArg(v_parser_116_, v_maxCount_117_, v___x_119_, v_a_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems(lean_object* v_00_u03b1_121_, lean_object* v_parser_122_, lean_object* v_maxCount_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v_parser_122_, v_maxCount_123_, v_a_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(lean_object* v_x_129_, lean_object* v_a_130_){
_start:
{
if (lean_obj_tag(v_x_129_) == 1)
{
lean_object* v_val_131_; lean_object* v___x_132_; 
v_val_131_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_val_131_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_a_130_);
lean_ctor_set(v___x_132_, 1, v_val_131_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___closed__1));
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v_a_130_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg___boxed(lean_object* v_x_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_135_, v_a_136_);
lean_dec(v_x_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(lean_object* v_00_u03b1_138_, lean_object* v_x_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_x_139_, v_a_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___boxed(lean_object* v_00_u03b1_142_, lean_object* v_x_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption(v_00_u03b1_142_, v_x_143_, v_a_144_);
lean_dec(v_x_143_);
return v_res_145_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(uint8_t v_c_146_){
_start:
{
uint32_t v___x_147_; uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_147_ = lean_uint8_to_uint32(v_c_146_);
v___x_158_ = 33;
v___x_159_ = lean_uint32_dec_eq(v___x_147_, v___x_158_);
if (v___x_159_ == 0)
{
uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_160_ = 35;
v___x_161_ = lean_uint32_dec_eq(v___x_147_, v___x_160_);
if (v___x_161_ == 0)
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 36;
v___x_163_ = lean_uint32_dec_eq(v___x_147_, v___x_162_);
if (v___x_163_ == 0)
{
uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_164_ = 37;
v___x_165_ = lean_uint32_dec_eq(v___x_147_, v___x_164_);
if (v___x_165_ == 0)
{
uint32_t v___x_166_; uint8_t v___x_167_; 
v___x_166_ = 38;
v___x_167_ = lean_uint32_dec_eq(v___x_147_, v___x_166_);
if (v___x_167_ == 0)
{
uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 39;
v___x_169_ = lean_uint32_dec_eq(v___x_147_, v___x_168_);
if (v___x_169_ == 0)
{
uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 42;
v___x_171_ = lean_uint32_dec_eq(v___x_147_, v___x_170_);
if (v___x_171_ == 0)
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 43;
v___x_173_ = lean_uint32_dec_eq(v___x_147_, v___x_172_);
if (v___x_173_ == 0)
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 45;
v___x_175_ = lean_uint32_dec_eq(v___x_147_, v___x_174_);
if (v___x_175_ == 0)
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 46;
v___x_177_ = lean_uint32_dec_eq(v___x_147_, v___x_176_);
if (v___x_177_ == 0)
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 94;
v___x_179_ = lean_uint32_dec_eq(v___x_147_, v___x_178_);
if (v___x_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 95;
v___x_181_ = lean_uint32_dec_eq(v___x_147_, v___x_180_);
if (v___x_181_ == 0)
{
uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = 96;
v___x_183_ = lean_uint32_dec_eq(v___x_147_, v___x_182_);
if (v___x_183_ == 0)
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 124;
v___x_185_ = lean_uint32_dec_eq(v___x_147_, v___x_184_);
if (v___x_185_ == 0)
{
uint32_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = 126;
v___x_187_ = lean_uint32_dec_eq(v___x_147_, v___x_186_);
if (v___x_187_ == 0)
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 48;
v___x_189_ = lean_uint32_dec_le(v___x_188_, v___x_147_);
if (v___x_189_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = 57;
v___x_191_ = lean_uint32_dec_le(v___x_147_, v___x_190_);
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
v___jp_148_:
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 97;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v___x_147_);
if (v___x_150_ == 0)
{
return v___x_150_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 122;
v___x_152_ = lean_uint32_dec_le(v___x_147_, v___x_151_);
return v___x_152_;
}
}
v___jp_153_:
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 65;
v___x_155_ = lean_uint32_dec_le(v___x_154_, v___x_147_);
if (v___x_155_ == 0)
{
goto v___jp_148_;
}
else
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 90;
v___x_157_ = lean_uint32_dec_le(v___x_147_, v___x_156_);
if (v___x_157_ == 0)
{
goto v___jp_148_;
}
else
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_146_ = stack[0].m_num;
uint8_t v_res_192_;
v_res_192_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_146_);
stack->m_num = v_res_192_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0___boxed(lean_object* v_c_193_){
_start:
{
uint8_t v_c_boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_c_boxed_194_ = lean_unbox(v_c_193_);
v_res_195_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___lam__0(v_c_boxed_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(lean_object* v_limit_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_snd_206_; lean_object* v_snd_207_; uint8_t v___x_208_; 
v___f_203_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_204_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_202_);
v___x_205_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_203_, v_limit_201_, v___x_204_, v_a_202_);
v_snd_206_ = lean_ctor_get(v___x_205_, 1);
lean_inc(v_snd_206_);
v_snd_207_ = lean_ctor_get(v_snd_206_, 1);
v___x_208_ = lean_unbox(v_snd_207_);
if (v___x_208_ == 0)
{
lean_object* v_fst_209_; lean_object* v_fst_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_238_; 
v_fst_209_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_fst_209_);
lean_dec_ref(v___x_205_);
v_fst_210_ = lean_ctor_get(v_snd_206_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_snd_206_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v_snd_206_, 1);
lean_dec(v_unused_239_);
v___x_212_ = v_snd_206_;
v_isShared_213_ = v_isSharedCheck_238_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_fst_210_);
lean_dec(v_snd_206_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_238_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
uint8_t v___x_214_; 
v___x_214_ = lean_nat_dec_eq(v_fst_209_, v___x_204_);
if (v___x_214_ == 0)
{
lean_object* v_array_215_; lean_object* v_idx_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_233_; 
lean_del_object(v___x_212_);
v_array_215_ = lean_ctor_get(v_a_202_, 0);
v_idx_216_ = lean_ctor_get(v_a_202_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_a_202_);
if (v_isSharedCheck_233_ == 0)
{
v___x_218_ = v_a_202_;
v_isShared_219_ = v_isSharedCheck_233_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_idx_216_);
lean_inc(v_array_215_);
lean_dec(v_a_202_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_233_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_lower_221_; lean_object* v_upper_222_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___y_230_; uint8_t v___x_232_; 
v___x_227_ = lean_nat_add(v_idx_216_, v_fst_209_);
lean_dec(v_fst_209_);
v___x_228_ = lean_byte_array_size(v_array_215_);
v___x_232_ = lean_nat_dec_le(v_idx_216_, v___x_204_);
if (v___x_232_ == 0)
{
v___y_230_ = v_idx_216_;
goto v___jp_229_;
}
else
{
lean_dec(v_idx_216_);
v___y_230_ = v___x_204_;
goto v___jp_229_;
}
v___jp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = l_ByteArray_toByteSlice(v_array_215_, v_lower_221_, v_upper_222_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v___x_223_);
lean_ctor_set(v___x_218_, 0, v_fst_210_);
v___x_225_ = v___x_218_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_fst_210_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
v___jp_229_:
{
uint8_t v___x_231_; 
v___x_231_ = lean_nat_dec_le(v___x_227_, v___x_228_);
if (v___x_231_ == 0)
{
lean_dec(v___x_227_);
v_lower_221_ = v___y_230_;
v_upper_222_ = v___x_228_;
goto v___jp_220_;
}
else
{
v_lower_221_ = v___y_230_;
v_upper_222_ = v___x_227_;
goto v___jp_220_;
}
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_236_; 
lean_dec(v_fst_210_);
lean_dec(v_fst_209_);
v___x_234_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 1);
lean_ctor_set(v___x_212_, 1, v___x_234_);
lean_ctor_set(v___x_212_, 0, v_a_202_);
v___x_236_ = v___x_212_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_202_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v_fst_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref(v___x_205_);
lean_dec_ref(v_a_202_);
v_fst_240_ = lean_ctor_get(v_snd_206_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_snd_206_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_snd_206_, 1);
lean_dec(v_unused_249_);
v___x_242_ = v_snd_206_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_fst_240_);
lean_dec(v_snd_206_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_box(0);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 1);
lean_ctor_set(v___x_242_, 1, v___x_244_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___boxed(lean_object* v_limit_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken(v_limit_250_, v_a_251_);
lean_dec(v_limit_250_);
return v_res_252_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__0));
v___x_255_ = lean_string_to_utf8(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf(lean_object* v_a_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_258_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_257_, v_a_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(lean_object* v_limits_262_, lean_object* v_a_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_array_265_; lean_object* v_idx_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_array_265_ = lean_ctor_get(v___y_264_, 0);
v_idx_266_ = lean_ctor_get(v___y_264_, 1);
v___x_267_ = lean_byte_array_size(v_array_265_);
v___x_268_ = lean_nat_dec_lt(v_idx_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___y_264_);
lean_ctor_set(v___x_269_, 1, v_a_263_);
return v___x_269_;
}
else
{
uint8_t v___x_270_; uint8_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_byte_array_fget(v_array_265_, v_idx_266_);
v___x_271_ = 13;
v___x_272_ = lean_uint8_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___y_264_);
lean_ctor_set(v___x_273_, 1, v_a_263_);
return v___x_273_;
}
else
{
lean_object* v_maxLeadingEmptyLines_274_; uint8_t v___x_275_; 
v_maxLeadingEmptyLines_274_ = lean_ctor_get(v_limits_262_, 9);
v___x_275_ = lean_nat_dec_le(v_maxLeadingEmptyLines_274_, v_a_263_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_277_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_276_, v___y_264_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_pos_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_pos_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_pos_278_);
lean_dec_ref_known(v___x_277_, 2);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_a_263_, v___x_279_);
lean_dec(v_a_263_);
v_a_263_ = v___x_280_;
v___y_264_ = v_pos_278_;
goto _start;
}
else
{
lean_object* v_pos_282_; lean_object* v_err_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_a_263_);
v_pos_282_ = lean_ctor_get(v___x_277_, 0);
v_err_283_ = lean_ctor_get(v___x_277_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_277_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_err_283_);
lean_inc(v_pos_282_);
lean_dec(v___x_277_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_pos_282_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_err_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_a_263_);
v___x_291_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___closed__1));
v___x_292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_292_, 0, v___y_264_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg___boxed(lean_object* v_limits_293_, lean_object* v_a_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_293_, v_a_294_, v___y_295_);
lean_dec_ref(v_limits_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(lean_object* v_limits_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_count_299_; lean_object* v___x_300_; 
v_count_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_297_, v_count_299_, v_a_298_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_pos_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_309_; 
v_pos_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v___x_300_, 1);
lean_dec(v_unused_310_);
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_pos_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_box(0);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_305_);
v___x_307_ = v___x_303_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_pos_301_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_pos_311_; lean_object* v_err_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_pos_311_ = lean_ctor_get(v___x_300_, 0);
v_err_312_ = lean_ctor_get(v___x_300_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_300_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_err_312_);
lean_inc(v_pos_311_);
lean_dec(v___x_300_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_pos_311_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_err_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines___boxed(lean_object* v_limits_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_320_, v_a_321_);
lean_dec_ref(v_limits_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(lean_object* v_limits_323_, lean_object* v_inst_324_, lean_object* v_a_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___redArg(v_limits_323_, v_a_325_, v___y_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0___boxed(lean_object* v_limits_328_, lean_object* v_inst_329_, lean_object* v_a_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines_spec__0(v_limits_328_, v_inst_329_, v_a_330_, v___y_331_);
lean_dec_ref(v_limits_328_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp(lean_object* v_a_336_){
_start:
{
lean_object* v_array_337_; lean_object* v_idx_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_array_337_ = lean_ctor_get(v_a_336_, 0);
v_idx_338_ = lean_ctor_get(v_a_336_, 1);
v___x_339_ = lean_byte_array_size(v_array_337_);
v___x_340_ = lean_nat_dec_lt(v_idx_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v_a_336_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
return v___x_342_;
}
else
{
uint8_t v___x_343_; uint8_t v_got_344_; uint8_t v___x_345_; 
v___x_343_ = 32;
v_got_344_ = lean_byte_array_fget(v_array_337_, v_idx_338_);
v___x_345_ = lean_uint8_dec_eq(v_got_344_, v___x_343_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_347_, 0, v_a_336_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
else
{
lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_358_; 
lean_inc(v_idx_338_);
lean_inc_ref(v_array_337_);
v_isSharedCheck_358_ = !lean_is_exclusive(v_a_336_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; lean_object* v_unused_360_; 
v_unused_359_ = lean_ctor_get(v_a_336_, 1);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_a_336_, 0);
lean_dec(v_unused_360_);
v___x_349_ = v_a_336_;
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
else
{
lean_dec(v_a_336_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_idx_338_, v___x_351_);
lean_dec(v_idx_338_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_352_);
v___x_354_ = v___x_349_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_array_337_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_352_);
v___x_354_ = v_reuseFailAlloc_357_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(lean_object* v_limits_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_pos_368_; lean_object* v_pos_372_; lean_object* v_maxSpaceSequence_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_snd_379_; lean_object* v_snd_380_; uint8_t v___x_381_; 
v_maxSpaceSequence_375_ = lean_ctor_get(v_limits_365_, 8);
v___x_376_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__2));
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___x_376_, v_maxSpaceSequence_375_, v___x_377_, v_a_366_);
v_snd_379_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_snd_379_);
lean_dec_ref(v___x_378_);
v_snd_380_ = lean_ctor_get(v_snd_379_, 1);
v___x_381_ = lean_unbox(v_snd_380_);
if (v___x_381_ == 0)
{
lean_object* v_fst_382_; lean_object* v_array_383_; lean_object* v_idx_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_fst_382_ = lean_ctor_get(v_snd_379_, 0);
lean_inc(v_fst_382_);
lean_dec(v_snd_379_);
v_array_383_ = lean_ctor_get(v_fst_382_, 0);
v_idx_384_ = lean_ctor_get(v_fst_382_, 1);
v___x_385_ = lean_byte_array_size(v_array_383_);
v___x_386_ = lean_nat_dec_lt(v_idx_384_, v___x_385_);
if (v___x_386_ == 0)
{
v_pos_368_ = v_fst_382_;
goto v___jp_367_;
}
else
{
uint8_t v___x_387_; uint32_t v___x_388_; uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_byte_array_fget(v_array_383_, v_idx_384_);
v___x_388_ = lean_uint8_to_uint32(v___x_387_);
v___x_389_ = 32;
v___x_390_ = lean_uint32_dec_eq(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 9;
v___x_392_ = lean_uint32_dec_eq(v___x_388_, v___x_391_);
if (v___x_392_ == 0)
{
v_pos_368_ = v_fst_382_;
goto v___jp_367_;
}
else
{
v_pos_372_ = v_fst_382_;
goto v___jp_371_;
}
}
else
{
v_pos_372_ = v_fst_382_;
goto v___jp_371_;
}
}
}
else
{
lean_object* v_fst_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_fst_393_ = lean_ctor_get(v_snd_379_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_snd_379_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v_snd_379_, 1);
lean_dec(v_unused_402_);
v___x_395_ = v_snd_379_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_fst_393_);
lean_dec(v_snd_379_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_box(0);
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 1);
lean_ctor_set(v___x_395_, 1, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_fst_393_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_pos_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
v___jp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v_pos_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___boxed(lean_object* v_limits_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows(v_limits_403_, v_a_404_);
lean_dec_ref(v_limits_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(lean_object* v_a_407_){
_start:
{
lean_object* v_array_408_; lean_object* v_idx_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_array_408_ = lean_ctor_get(v_a_407_, 0);
v_idx_409_ = lean_ctor_get(v_a_407_, 1);
v___x_410_ = lean_byte_array_size(v_array_408_);
v___x_411_ = lean_nat_dec_lt(v_idx_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_box(0);
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v_a_407_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
return v___x_413_;
}
else
{
lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_469_; 
lean_inc(v_idx_409_);
lean_inc_ref(v_array_408_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_470_ = lean_ctor_get(v_a_407_, 1);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_a_407_, 0);
lean_dec(v_unused_471_);
v___x_415_ = v_a_407_;
v_isShared_416_ = v_isSharedCheck_469_;
goto v_resetjp_414_;
}
else
{
lean_dec(v_a_407_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_469_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
uint8_t v_c_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_it_x27_421_; 
v_c_417_ = lean_byte_array_fget(v_array_408_, v_idx_409_);
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_idx_409_, v___x_418_);
lean_dec(v_idx_409_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_419_);
v_it_x27_421_ = v___x_415_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_array_408_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_419_);
v_it_x27_421_ = v_reuseFailAlloc_468_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
uint8_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 48;
v___x_465_ = lean_uint8_dec_le(v___x_464_, v_c_417_);
if (v___x_465_ == 0)
{
goto v___jp_459_;
}
else
{
uint8_t v___x_466_; uint8_t v___x_467_; 
v___x_466_ = 57;
v___x_467_ = lean_uint8_dec_le(v_c_417_, v___x_466_);
if (v___x_467_ == 0)
{
goto v___jp_459_;
}
else
{
goto v___jp_439_;
}
}
v___jp_422_:
{
uint8_t v___x_423_; uint8_t v___x_424_; uint8_t v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_423_ = 97;
v___x_424_ = lean_uint8_sub(v_c_417_, v___x_423_);
v___x_425_ = 10;
v___x_426_ = lean_uint8_add(v___x_424_, v___x_425_);
v___x_427_ = lean_box(v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_it_x27_421_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
return v___x_428_;
}
v___jp_429_:
{
uint8_t v___x_430_; uint8_t v___x_431_; 
v___x_430_ = 65;
v___x_431_ = lean_uint8_dec_le(v___x_430_, v_c_417_);
if (v___x_431_ == 0)
{
goto v___jp_422_;
}
else
{
uint8_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = 70;
v___x_433_ = lean_uint8_dec_le(v_c_417_, v___x_432_);
if (v___x_433_ == 0)
{
goto v___jp_422_;
}
else
{
uint8_t v___x_434_; uint8_t v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_434_ = lean_uint8_sub(v_c_417_, v___x_430_);
v___x_435_ = 10;
v___x_436_ = lean_uint8_add(v___x_434_, v___x_435_);
v___x_437_ = lean_box(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v_it_x27_421_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
return v___x_438_;
}
}
}
v___jp_439_:
{
uint8_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = 48;
v___x_441_ = lean_uint8_dec_le(v___x_440_, v_c_417_);
if (v___x_441_ == 0)
{
goto v___jp_429_;
}
else
{
uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = 57;
v___x_443_ = lean_uint8_dec_le(v_c_417_, v___x_442_);
if (v___x_443_ == 0)
{
goto v___jp_429_;
}
else
{
uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_uint8_sub(v_c_417_, v___x_440_);
v___x_445_ = lean_box(v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_it_x27_421_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
return v___x_446_;
}
}
}
v___jp_447_:
{
lean_object* v___x_448_; uint32_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit___closed__0));
v___x_449_ = lean_uint8_to_uint32(v_c_417_);
v___x_450_ = l_Char_quote(v___x_449_);
v___x_451_ = lean_string_append(v___x_448_, v___x_450_);
lean_dec_ref(v___x_450_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v_it_x27_421_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
return v___x_453_;
}
v___jp_454_:
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 65;
v___x_456_ = lean_uint8_dec_le(v___x_455_, v_c_417_);
if (v___x_456_ == 0)
{
goto v___jp_447_;
}
else
{
uint8_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 70;
v___x_458_ = lean_uint8_dec_le(v_c_417_, v___x_457_);
if (v___x_458_ == 0)
{
goto v___jp_447_;
}
else
{
goto v___jp_439_;
}
}
}
v___jp_459_:
{
uint8_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = 97;
v___x_461_ = lean_uint8_dec_le(v___x_460_, v_c_417_);
if (v___x_461_ == 0)
{
goto v___jp_454_;
}
else
{
uint8_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = 102;
v___x_463_ = lean_uint8_dec_le(v_c_417_, v___x_462_);
if (v___x_463_ == 0)
{
goto v___jp_454_;
}
else
{
goto v___jp_439_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(lean_object* v_acc_478_, lean_object* v_count_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_pos_482_; lean_object* v_err_483_; lean_object* v___x_511_; 
lean_inc_ref(v_a_480_);
v___x_511_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_480_);
if (lean_obj_tag(v___x_511_) == 0)
{
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_pos_512_; lean_object* v_res_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_a_480_);
v_pos_512_ = lean_ctor_get(v___x_511_, 0);
v_res_513_ = lean_ctor_get(v___x_511_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_530_ == 0)
{
v___x_515_ = v___x_511_;
v_isShared_516_ = v_isSharedCheck_530_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_res_513_);
lean_inc(v_pos_512_);
lean_dec(v___x_511_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_530_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_517_ = lean_unsigned_to_nat(16u);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_count_479_, v___x_518_);
lean_dec(v_count_479_);
v___x_520_ = lean_nat_dec_lt(v___x_517_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
lean_del_object(v___x_515_);
v___x_521_ = lean_nat_mul(v_acc_478_, v___x_517_);
lean_dec(v_acc_478_);
v___x_522_ = lean_unbox(v_res_513_);
lean_dec(v_res_513_);
v___x_523_ = lean_uint8_to_nat(v___x_522_);
v___x_524_ = lean_nat_add(v___x_521_, v___x_523_);
lean_dec(v___x_521_);
v_acc_478_ = v___x_524_;
v_count_479_ = v___x_519_;
v_a_480_ = v_pos_512_;
goto _start;
}
else
{
lean_object* v___x_526_; lean_object* v___x_528_; 
lean_dec(v___x_519_);
lean_dec(v_res_513_);
lean_dec(v_acc_478_);
v___x_526_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 1);
lean_ctor_set(v___x_515_, 1, v___x_526_);
v___x_528_ = v___x_515_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_pos_512_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_pos_531_; lean_object* v_err_532_; 
v_pos_531_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_pos_531_);
v_err_532_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_err_532_);
lean_dec_ref_known(v___x_511_, 2);
v_pos_482_ = v_pos_531_;
v_err_483_ = v_err_532_;
goto v___jp_481_;
}
}
else
{
lean_object* v_err_533_; 
v_err_533_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_err_533_);
lean_dec_ref_known(v___x_511_, 2);
lean_inc_ref(v_a_480_);
v_pos_482_ = v_a_480_;
v_err_483_ = v_err_533_;
goto v___jp_481_;
}
v___jp_481_:
{
lean_object* v_idx_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_509_; 
v_idx_484_ = lean_ctor_get(v_a_480_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v_a_480_, 0);
lean_dec(v_unused_510_);
v___x_486_ = v_a_480_;
v_isShared_487_ = v_isSharedCheck_509_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_idx_484_);
lean_dec(v_a_480_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_509_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v_array_488_; lean_object* v_idx_489_; uint8_t v___x_490_; 
v_array_488_ = lean_ctor_get(v_pos_482_, 0);
v_idx_489_ = lean_ctor_get(v_pos_482_, 1);
v___x_490_ = lean_nat_dec_eq(v_idx_484_, v_idx_489_);
lean_dec(v_idx_484_);
if (v___x_490_ == 0)
{
lean_object* v___x_492_; 
lean_dec(v_count_479_);
lean_dec(v_acc_478_);
if (v_isShared_487_ == 0)
{
lean_ctor_set_tag(v___x_486_, 1);
lean_ctor_set(v___x_486_, 1, v_err_483_);
lean_ctor_set(v___x_486_, 0, v_pos_482_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_pos_482_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_err_483_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; 
lean_dec(v_err_483_);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_nat_dec_eq(v_count_479_, v___x_494_);
lean_dec(v_count_479_);
if (v___x_495_ == 0)
{
lean_object* v___x_497_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_acc_478_);
lean_ctor_set(v___x_486_, 0, v_pos_482_);
v___x_497_ = v___x_486_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_pos_482_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_acc_478_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
lean_dec(v_acc_478_);
v___x_499_ = lean_byte_array_size(v_array_488_);
v___x_500_ = lean_nat_dec_lt(v_idx_489_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_box(0);
if (v_isShared_487_ == 0)
{
lean_ctor_set_tag(v___x_486_, 1);
lean_ctor_set(v___x_486_, 1, v___x_501_);
lean_ctor_set(v___x_486_, 0, v_pos_482_);
v___x_503_ = v___x_486_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_pos_482_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_487_ == 0)
{
lean_ctor_set_tag(v___x_486_, 1);
lean_ctor_set(v___x_486_, 1, v___x_505_);
lean_ctor_set(v___x_486_, 0, v_pos_482_);
v___x_507_ = v___x_486_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_pos_482_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_535_, v___x_535_, v_a_534_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_539_ = lean_string_to_utf8(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_548_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_547_, v_a_546_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_pos_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_610_; 
v_pos_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_548_, 1);
lean_dec(v_unused_611_);
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_610_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_pos_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_610_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_array_558_; lean_object* v_idx_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_array_558_ = lean_ctor_get(v_pos_549_, 0);
v_idx_559_ = lean_ctor_get(v_pos_549_, 1);
v___x_560_ = lean_byte_array_size(v_array_558_);
v___x_561_ = lean_nat_dec_lt(v_idx_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_del_object(v___x_551_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v_pos_549_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
return v___x_563_;
}
else
{
uint8_t v_c_564_; uint8_t v___x_565_; uint8_t v___x_566_; 
v_c_564_ = lean_byte_array_fget(v_array_558_, v_idx_559_);
v___x_565_ = 48;
v___x_566_ = lean_uint8_dec_le(v___x_565_, v_c_564_);
if (v___x_566_ == 0)
{
goto v___jp_553_;
}
else
{
uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 57;
v___x_568_ = lean_uint8_dec_le(v_c_564_, v___x_567_);
if (v___x_568_ == 0)
{
goto v___jp_553_;
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_607_; 
lean_inc(v_idx_559_);
lean_inc_ref(v_array_558_);
lean_del_object(v___x_551_);
v_isSharedCheck_607_ = !lean_is_exclusive(v_pos_549_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; lean_object* v_unused_609_; 
v_unused_608_ = lean_ctor_get(v_pos_549_, 1);
lean_dec(v_unused_608_);
v_unused_609_ = lean_ctor_get(v_pos_549_, 0);
lean_dec(v_unused_609_);
v___x_570_ = v_pos_549_;
v_isShared_571_ = v_isSharedCheck_607_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_pos_549_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_607_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_it_x27_575_; 
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v_idx_559_, v___x_572_);
lean_dec(v_idx_559_);
lean_inc(v___x_573_);
lean_inc_ref(v_array_558_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_573_);
v_it_x27_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_array_558_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_573_);
v_it_x27_575_ = v_reuseFailAlloc_606_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
uint8_t v___x_576_; 
v___x_576_ = lean_nat_dec_lt(v___x_573_, v___x_560_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v___x_573_);
lean_dec_ref(v_array_558_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v_it_x27_575_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
else
{
uint8_t v___x_579_; uint8_t v_got_580_; uint8_t v___x_581_; 
v___x_579_ = 46;
v_got_580_ = lean_byte_array_fget(v_array_558_, v___x_573_);
v___x_581_ = lean_uint8_dec_eq(v_got_580_, v___x_579_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___x_573_);
lean_dec_ref(v_array_558_);
v___x_582_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5));
v___x_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_583_, 0, v_it_x27_575_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_589_; 
lean_dec_ref(v_it_x27_575_);
v___x_584_ = lean_nat_add(v___x_573_, v___x_572_);
lean_dec(v___x_573_);
lean_inc(v___x_584_);
lean_inc_ref(v_array_558_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_array_558_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_589_ = lean_nat_dec_lt(v___x_584_, v___x_560_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v___x_584_);
lean_dec_ref(v_array_558_);
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_585_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
else
{
uint8_t v_c_592_; uint8_t v___x_593_; 
v_c_592_ = lean_byte_array_fget(v_array_558_, v___x_584_);
v___x_593_ = lean_uint8_dec_le(v___x_565_, v_c_592_);
if (v___x_593_ == 0)
{
lean_dec(v___x_584_);
lean_dec_ref(v_array_558_);
goto v___jp_586_;
}
else
{
uint8_t v___x_594_; 
v___x_594_ = lean_uint8_dec_le(v_c_592_, v___x_567_);
if (v___x_594_ == 0)
{
lean_dec(v___x_584_);
lean_dec_ref(v_array_558_);
goto v___jp_586_;
}
else
{
lean_object* v___x_595_; uint32_t v___x_596_; lean_object* v___x_597_; lean_object* v_it_x27_598_; uint32_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec_ref_known(v___x_585_, 2);
v___x_595_ = lean_unsigned_to_nat(48u);
v___x_596_ = lean_uint8_to_uint32(v_c_564_);
v___x_597_ = lean_nat_add(v___x_584_, v___x_572_);
lean_dec(v___x_584_);
v_it_x27_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_598_, 0, v_array_558_);
lean_ctor_set(v_it_x27_598_, 1, v___x_597_);
v___x_599_ = lean_uint8_to_uint32(v_c_592_);
v___x_600_ = lean_uint32_to_nat(v___x_596_);
v___x_601_ = lean_nat_sub(v___x_600_, v___x_595_);
lean_dec(v___x_600_);
v___x_602_ = lean_uint32_to_nat(v___x_599_);
v___x_603_ = lean_nat_sub(v___x_602_, v___x_595_);
lean_dec(v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_601_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v_it_x27_598_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
}
}
v___jp_586_:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_585_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
return v___x_588_;
}
}
}
}
}
}
}
}
v___jp_553_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 1);
lean_ctor_set(v___x_551_, 1, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_pos_549_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_object* v_pos_612_; lean_object* v_err_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
v_pos_612_ = lean_ctor_get(v___x_548_, 0);
v_err_613_ = lean_ctor_get(v___x_548_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_548_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_err_613_);
lean_inc(v_pos_612_);
lean_dec(v___x_548_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_pos_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_err_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_res_623_; lean_object* v_pos_624_; lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_res_623_ = lean_ctor_get(v___x_622_, 1);
lean_inc(v_res_623_);
v_pos_624_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_pos_624_);
lean_dec_ref_known(v___x_622_, 2);
v_fst_625_ = lean_ctor_get(v_res_623_, 0);
lean_inc(v_fst_625_);
v_snd_626_ = lean_ctor_get(v_res_623_, 1);
lean_inc(v_snd_626_);
lean_dec(v_res_623_);
v___x_627_ = l_Std_Http_Version_ofNumber_x3f(v_fst_625_, v_snd_626_);
lean_dec(v_snd_626_);
lean_dec(v_fst_625_);
v___x_628_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_627_, v_pos_624_);
lean_dec(v___x_627_);
return v___x_628_;
}
else
{
lean_object* v_pos_629_; lean_object* v_err_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_pos_629_ = lean_ctor_get(v___x_622_, 0);
v_err_630_ = lean_ctor_get(v___x_622_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_622_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_err_630_);
lean_inc(v_pos_629_);
lean_dec(v___x_622_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_pos_629_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_err_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object* v_a_638_, lean_object* v_f_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_apply_1(v_a_638_, v___y_640_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_pos_642_; lean_object* v_res_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_pos_642_ = lean_ctor_get(v___x_641_, 0);
v_res_643_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v___x_641_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_res_643_);
lean_inc(v_pos_642_);
lean_dec(v___x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_apply_1(v_f_639_, v_res_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_pos_642_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
lean_object* v_pos_652_; lean_object* v_err_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_f_639_);
v_pos_652_ = lean_ctor_get(v___x_641_, 0);
v_err_653_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_641_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_err_653_);
lean_inc(v_pos_652_);
lean_dec(v___x_641_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_pos_652_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_err_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_a_663_, lean_object* v_f_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v_a_663_, v_f_664_, v___y_665_);
return v___x_666_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object* v_x_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = 9;
return v___x_668_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_667_ = stack[0].m_obj;
uint8_t v_res_669_;
v_res_669_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_667_);
stack->m_num = v_res_669_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_670_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object* v_x_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = 32;
return v___x_674_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_673_ = stack[0].m_obj;
uint8_t v_res_675_;
v_res_675_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_673_);
stack->m_num = v_res_675_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object* v_x_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_676_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object* v_x_679_){
_start:
{
uint8_t v___x_680_; 
v___x_680_ = 28;
return v___x_680_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_679_ = stack[0].m_obj;
uint8_t v_res_681_;
v_res_681_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_679_);
stack->m_num = v_res_681_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object* v_x_682_){
_start:
{
uint8_t v_res_683_; lean_object* v_r_684_; 
v_res_683_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_682_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object* v_x_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = 1;
return v___x_686_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_685_ = stack[0].m_obj;
uint8_t v_res_687_;
v_res_687_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_685_);
stack->m_num = v_res_687_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object* v_x_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object* v_x_691_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = 5;
return v___x_692_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_691_ = stack[0].m_obj;
uint8_t v_res_693_;
v_res_693_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_691_);
stack->m_num = v_res_693_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object* v_x_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_694_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object* v_x_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = 4;
return v___x_698_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_697_ = stack[0].m_obj;
uint8_t v_res_699_;
v_res_699_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_697_);
stack->m_num = v_res_699_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object* v_x_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_700_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object* v_x_703_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = 10;
return v___x_704_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_703_ = stack[0].m_obj;
uint8_t v_res_705_;
v_res_705_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_703_);
stack->m_num = v_res_705_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object* v_x_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object* v_x_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = 12;
return v___x_710_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_709_ = stack[0].m_obj;
uint8_t v_res_711_;
v_res_711_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_709_);
stack->m_num = v_res_711_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object* v_x_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_712_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object* v_x_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = 14;
return v___x_716_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_715_ = stack[0].m_obj;
uint8_t v_res_717_;
v_res_717_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(v_x_715_);
stack->m_num = v_res_717_;
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
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object* v_x_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = 16;
return v___x_722_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_721_ = stack[0].m_obj;
uint8_t v_res_723_;
v_res_723_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_721_);
stack->m_num = v_res_723_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object* v_x_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_724_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object* v_x_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = 18;
return v___x_728_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_727_ = stack[0].m_obj;
uint8_t v_res_729_;
v_res_729_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_727_);
stack->m_num = v_res_729_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object* v_x_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_730_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object* v_x_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = 20;
return v___x_734_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_733_ = stack[0].m_obj;
uint8_t v_res_735_;
v_res_735_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_733_);
stack->m_num = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object* v_x_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_736_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object* v_x_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = 23;
return v___x_740_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_739_ = stack[0].m_obj;
uint8_t v_res_741_;
v_res_741_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_739_);
stack->m_num = v_res_741_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object* v_x_742_){
_start:
{
uint8_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_742_);
v_r_744_ = lean_box(v_res_743_);
return v_r_744_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object* v_x_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = 22;
return v___x_746_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_745_ = stack[0].m_obj;
uint8_t v_res_747_;
v_res_747_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_745_);
stack->m_num = v_res_747_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object* v_x_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_748_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object* v_x_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = 25;
return v___x_752_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_751_ = stack[0].m_obj;
uint8_t v_res_753_;
v_res_753_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_751_);
stack->m_num = v_res_753_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object* v_x_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_754_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object* v_x_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = 29;
return v___x_758_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_757_ = stack[0].m_obj;
uint8_t v_res_759_;
v_res_759_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_757_);
stack->m_num = v_res_759_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object* v_x_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = 33;
return v___x_764_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_763_ = stack[0].m_obj;
uint8_t v_res_765_;
v_res_765_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_763_);
stack->m_num = v_res_765_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object* v_x_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_766_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object* v_x_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = 35;
return v___x_770_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_769_ = stack[0].m_obj;
uint8_t v_res_771_;
v_res_771_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_769_);
stack->m_num = v_res_771_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object* v_x_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_772_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object* v_x_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = 38;
return v___x_776_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_775_ = stack[0].m_obj;
uint8_t v_res_777_;
v_res_777_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_775_);
stack->m_num = v_res_777_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object* v_x_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_778_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object* v_x_781_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = 39;
return v___x_782_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_781_ = stack[0].m_obj;
uint8_t v_res_783_;
v_res_783_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_781_);
stack->m_num = v_res_783_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object* v_x_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object* v_x_787_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = 37;
return v___x_788_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_787_ = stack[0].m_obj;
uint8_t v_res_789_;
v_res_789_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_787_);
stack->m_num = v_res_789_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_790_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object* v_x_793_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = 36;
return v___x_794_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_793_ = stack[0].m_obj;
uint8_t v_res_795_;
v_res_795_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_793_);
stack->m_num = v_res_795_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object* v_x_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object* v_x_799_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = 34;
return v___x_800_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_799_ = stack[0].m_obj;
uint8_t v_res_801_;
v_res_801_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_799_);
stack->m_num = v_res_801_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object* v_x_802_){
_start:
{
uint8_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_802_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object* v_x_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = 30;
return v___x_806_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_805_ = stack[0].m_obj;
uint8_t v_res_807_;
v_res_807_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_805_);
stack->m_num = v_res_807_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object* v_x_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_808_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object* v_x_811_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = 26;
return v___x_812_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_811_ = stack[0].m_obj;
uint8_t v_res_813_;
v_res_813_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_811_);
stack->m_num = v_res_813_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object* v_x_814_){
_start:
{
uint8_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_814_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = 24;
return v___x_818_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_817_ = stack[0].m_obj;
uint8_t v_res_819_;
v_res_819_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_817_);
stack->m_num = v_res_819_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object* v_x_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_820_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object* v_x_823_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = 27;
return v___x_824_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_823_ = stack[0].m_obj;
uint8_t v_res_825_;
v_res_825_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_823_);
stack->m_num = v_res_825_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_826_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object* v_x_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = 21;
return v___x_830_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_829_ = stack[0].m_obj;
uint8_t v_res_831_;
v_res_831_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_829_);
stack->m_num = v_res_831_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_832_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object* v_x_835_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = 19;
return v___x_836_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_835_ = stack[0].m_obj;
uint8_t v_res_837_;
v_res_837_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_835_);
stack->m_num = v_res_837_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object* v_x_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_838_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object* v_x_841_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = 17;
return v___x_842_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_841_ = stack[0].m_obj;
uint8_t v_res_843_;
v_res_843_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_841_);
stack->m_num = v_res_843_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object* v_x_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_844_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object* v_x_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = 15;
return v___x_848_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_847_ = stack[0].m_obj;
uint8_t v_res_849_;
v_res_849_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_847_);
stack->m_num = v_res_849_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object* v_x_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_850_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object* v_x_853_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = 13;
return v___x_854_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_853_ = stack[0].m_obj;
uint8_t v_res_855_;
v_res_855_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_853_);
stack->m_num = v_res_855_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object* v_x_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_856_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object* v_x_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = 11;
return v___x_860_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_859_ = stack[0].m_obj;
uint8_t v_res_861_;
v_res_861_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_859_);
stack->m_num = v_res_861_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object* v_x_862_){
_start:
{
uint8_t v_res_863_; lean_object* v_r_864_; 
v_res_863_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_862_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object* v_x_865_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = 6;
return v___x_866_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_865_ = stack[0].m_obj;
uint8_t v_res_867_;
v_res_867_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_865_);
stack->m_num = v_res_867_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object* v_x_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_868_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object* v_x_871_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = 3;
return v___x_872_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_871_ = stack[0].m_obj;
uint8_t v_res_873_;
v_res_873_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_871_);
stack->m_num = v_res_873_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object* v_x_874_){
_start:
{
uint8_t v_res_875_; lean_object* v_r_876_; 
v_res_875_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_874_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object* v_x_877_){
_start:
{
uint8_t v___x_878_; 
v___x_878_ = 2;
return v___x_878_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_877_ = stack[0].m_obj;
uint8_t v_res_879_;
v_res_879_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_877_);
stack->m_num = v_res_879_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object* v_x_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_880_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object* v_x_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = 31;
return v___x_884_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_883_ = stack[0].m_obj;
uint8_t v_res_885_;
v_res_885_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_883_);
stack->m_num = v_res_885_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object* v_x_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_886_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object* v_x_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = 0;
return v___x_890_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_889_ = stack[0].m_obj;
uint8_t v_res_891_;
v_res_891_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_889_);
stack->m_num = v_res_891_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object* v_x_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_892_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object* v_x_895_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = 7;
return v___x_896_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_895_ = stack[0].m_obj;
uint8_t v_res_897_;
v_res_897_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_895_);
stack->m_num = v_res_897_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object* v_x_898_){
_start:
{
uint8_t v_res_899_; lean_object* v_r_900_; 
v_res_899_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_898_);
v_r_900_ = lean_box(v_res_899_);
return v_r_900_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object* v_x_901_){
_start:
{
uint8_t v___x_902_; 
v___x_902_ = 8;
return v___x_902_;
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_901_ = stack[0].m_obj;
uint8_t v_res_903_;
v_res_903_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_901_);
stack->m_num = v_res_903_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object* v_x_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_904_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22));
v___x_932_ = lean_string_to_utf8(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23);
v___x_934_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26));
v___x_938_ = lean_string_to_utf8(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27);
v___x_940_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29));
v___x_943_ = lean_string_to_utf8(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30);
v___x_945_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33));
v___x_949_ = lean_string_to_utf8(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34);
v___x_951_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36));
v___x_954_ = lean_string_to_utf8(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37);
v___x_956_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40));
v___x_960_ = lean_string_to_utf8(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41);
v___x_962_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43));
v___x_965_ = lean_string_to_utf8(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44);
v___x_967_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47));
v___x_971_ = lean_string_to_utf8(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48);
v___x_973_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50));
v___x_976_ = lean_string_to_utf8(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51);
v___x_978_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54));
v___x_982_ = lean_string_to_utf8(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55);
v___x_984_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57));
v___x_987_ = lean_string_to_utf8(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58);
v___x_989_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61));
v___x_993_ = lean_string_to_utf8(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62);
v___x_995_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64));
v___x_998_ = lean_string_to_utf8(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65);
v___x_1000_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68));
v___x_1004_ = lean_string_to_utf8(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69);
v___x_1006_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71));
v___x_1009_ = lean_string_to_utf8(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72);
v___x_1011_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75));
v___x_1015_ = lean_string_to_utf8(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76);
v___x_1017_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78));
v___x_1020_ = lean_string_to_utf8(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79);
v___x_1022_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82));
v___x_1026_ = lean_string_to_utf8(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83);
v___x_1028_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85));
v___x_1031_ = lean_string_to_utf8(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86);
v___x_1033_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89));
v___x_1037_ = lean_string_to_utf8(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90);
v___x_1039_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92));
v___x_1042_ = lean_string_to_utf8(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93);
v___x_1044_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96));
v___x_1048_ = lean_string_to_utf8(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97);
v___x_1050_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99));
v___x_1053_ = lean_string_to_utf8(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100);
v___x_1055_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103));
v___x_1059_ = lean_string_to_utf8(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104);
v___x_1061_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106));
v___x_1064_ = lean_string_to_utf8(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107);
v___x_1066_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110));
v___x_1070_ = lean_string_to_utf8(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111);
v___x_1072_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113));
v___x_1075_ = lean_string_to_utf8(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114);
v___x_1077_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117));
v___x_1081_ = lean_string_to_utf8(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118);
v___x_1083_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120));
v___x_1086_ = lean_string_to_utf8(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121);
v___x_1088_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124));
v___x_1092_ = lean_string_to_utf8(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125);
v___x_1094_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127));
v___x_1097_ = lean_string_to_utf8(v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128);
v___x_1099_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131));
v___x_1103_ = lean_string_to_utf8(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132);
v___x_1105_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134));
v___x_1108_ = lean_string_to_utf8(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135);
v___x_1110_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138));
v___x_1114_ = lean_string_to_utf8(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139);
v___x_1116_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141));
v___x_1119_ = lean_string_to_utf8(v___x_1118_);
return v___x_1119_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142);
v___x_1121_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145));
v___x_1125_ = lean_string_to_utf8(v___x_1124_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146);
v___x_1127_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148));
v___x_1130_ = lean_string_to_utf8(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149);
v___x_1132_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152));
v___x_1136_ = lean_string_to_utf8(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153);
v___x_1138_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155));
v___x_1141_ = lean_string_to_utf8(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156);
v___x_1143_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159));
v___x_1147_ = lean_string_to_utf8(v___x_1146_);
return v___x_1147_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160);
v___x_1149_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_1150_){
_start:
{
lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___f_1153_; lean_object* v___f_1154_; lean_object* v___f_1155_; lean_object* v___f_1156_; lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v_idx_1173_; lean_object* v___y_1174_; lean_object* v_pos_1175_; lean_object* v_idx_1176_; lean_object* v_idx_1211_; lean_object* v___y_1212_; lean_object* v_pos_1213_; lean_object* v_idx_1214_; lean_object* v___f_1229_; lean_object* v_idx_1231_; lean_object* v___y_1232_; lean_object* v_pos_1233_; lean_object* v_idx_1234_; lean_object* v_idx_1250_; lean_object* v___y_1251_; lean_object* v_pos_1252_; lean_object* v_idx_1253_; lean_object* v___f_1268_; lean_object* v_idx_1270_; lean_object* v___y_1271_; lean_object* v_pos_1272_; lean_object* v_idx_1273_; lean_object* v_idx_1289_; lean_object* v___y_1290_; lean_object* v_pos_1291_; lean_object* v_idx_1292_; lean_object* v___f_1307_; lean_object* v_idx_1309_; lean_object* v___y_1310_; lean_object* v_pos_1311_; lean_object* v_idx_1312_; lean_object* v_idx_1328_; lean_object* v___y_1329_; lean_object* v_pos_1330_; lean_object* v_idx_1331_; lean_object* v___f_1346_; lean_object* v_idx_1348_; lean_object* v___y_1349_; lean_object* v_pos_1350_; lean_object* v_idx_1351_; lean_object* v_idx_1367_; lean_object* v___y_1368_; lean_object* v_pos_1369_; lean_object* v_idx_1370_; lean_object* v___f_1385_; lean_object* v_idx_1387_; lean_object* v___y_1388_; lean_object* v_pos_1389_; lean_object* v_idx_1390_; lean_object* v_idx_1406_; lean_object* v___y_1407_; lean_object* v_pos_1408_; lean_object* v_idx_1409_; lean_object* v___f_1424_; lean_object* v_idx_1426_; lean_object* v___y_1427_; lean_object* v_pos_1428_; lean_object* v_idx_1429_; lean_object* v_idx_1445_; lean_object* v___y_1446_; lean_object* v_pos_1447_; lean_object* v_idx_1448_; lean_object* v___f_1463_; lean_object* v_idx_1465_; lean_object* v___y_1466_; lean_object* v_pos_1467_; lean_object* v_idx_1468_; lean_object* v_idx_1484_; lean_object* v___y_1485_; lean_object* v_pos_1486_; lean_object* v_idx_1487_; lean_object* v___f_1502_; lean_object* v_idx_1504_; lean_object* v___y_1505_; lean_object* v_pos_1506_; lean_object* v_idx_1507_; lean_object* v_idx_1523_; lean_object* v___y_1524_; lean_object* v_pos_1525_; lean_object* v_idx_1526_; lean_object* v___f_1541_; lean_object* v_idx_1543_; lean_object* v___y_1544_; lean_object* v_pos_1545_; lean_object* v_idx_1546_; lean_object* v_idx_1562_; lean_object* v___y_1563_; lean_object* v_pos_1564_; lean_object* v_idx_1565_; lean_object* v___f_1580_; lean_object* v_idx_1582_; lean_object* v___y_1583_; lean_object* v_pos_1584_; lean_object* v_idx_1585_; lean_object* v_idx_1601_; lean_object* v___y_1602_; lean_object* v_pos_1603_; lean_object* v_idx_1604_; lean_object* v___f_1619_; lean_object* v_idx_1621_; lean_object* v___y_1622_; lean_object* v_pos_1623_; lean_object* v_idx_1624_; lean_object* v_idx_1640_; lean_object* v___y_1641_; lean_object* v_pos_1642_; lean_object* v_idx_1643_; lean_object* v___f_1658_; lean_object* v_idx_1660_; lean_object* v___y_1661_; lean_object* v_pos_1662_; lean_object* v_idx_1663_; lean_object* v_idx_1679_; lean_object* v___y_1680_; lean_object* v_pos_1681_; lean_object* v_idx_1682_; lean_object* v___f_1697_; lean_object* v_idx_1699_; lean_object* v___y_1700_; lean_object* v_pos_1701_; lean_object* v_idx_1702_; lean_object* v_idx_1718_; lean_object* v___y_1719_; lean_object* v_pos_1720_; lean_object* v_idx_1721_; lean_object* v___f_1736_; lean_object* v_idx_1738_; lean_object* v___y_1739_; lean_object* v_pos_1740_; lean_object* v_idx_1741_; lean_object* v_idx_1757_; lean_object* v___y_1758_; lean_object* v_pos_1759_; lean_object* v_idx_1760_; lean_object* v___f_1775_; lean_object* v_idx_1777_; lean_object* v___y_1778_; lean_object* v_pos_1779_; lean_object* v_idx_1780_; lean_object* v_idx_1796_; lean_object* v___y_1797_; lean_object* v_pos_1798_; lean_object* v_idx_1799_; lean_object* v___f_1814_; lean_object* v_idx_1816_; lean_object* v___y_1817_; lean_object* v_pos_1818_; lean_object* v_idx_1819_; lean_object* v_idx_1835_; lean_object* v___y_1836_; lean_object* v_pos_1837_; lean_object* v_idx_1838_; lean_object* v___f_1853_; lean_object* v_idx_1855_; lean_object* v___y_1856_; lean_object* v_pos_1857_; lean_object* v_idx_1858_; lean_object* v_idx_1874_; lean_object* v___y_1875_; lean_object* v_pos_1876_; lean_object* v_idx_1877_; lean_object* v___f_1892_; lean_object* v_idx_1894_; lean_object* v___y_1895_; lean_object* v_pos_1896_; lean_object* v_idx_1897_; lean_object* v_idx_1913_; lean_object* v___y_1914_; lean_object* v_pos_1915_; lean_object* v_idx_1916_; lean_object* v___f_1931_; lean_object* v_idx_1933_; lean_object* v___y_1934_; lean_object* v_pos_1935_; lean_object* v_idx_1936_; lean_object* v___y_1952_; lean_object* v_pos_1953_; lean_object* v___f_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___f_1151_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0));
v___f_1152_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___f_1153_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2));
v___f_1154_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
v___f_1155_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4));
v___f_1156_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5));
v___f_1157_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6));
v___f_1158_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7));
v___f_1159_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8));
v___f_1160_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9));
v___f_1161_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10));
v___f_1162_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11));
v___f_1163_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12));
v___f_1164_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13));
v___f_1165_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14));
v___f_1166_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15));
v___f_1167_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16));
v___f_1168_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17));
v___f_1169_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18));
v___f_1170_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19));
v___f_1171_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___f_1229_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25));
v___f_1268_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32));
v___f_1307_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39));
v___f_1346_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46));
v___f_1385_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53));
v___f_1424_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60));
v___f_1463_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67));
v___f_1502_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74));
v___f_1541_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81));
v___f_1580_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88));
v___f_1619_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95));
v___f_1658_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102));
v___f_1697_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109));
v___f_1736_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116));
v___f_1775_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123));
v___f_1814_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130));
v___f_1853_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137));
v___f_1892_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144));
v___f_1931_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151));
v___f_1970_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158));
v___x_1971_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161);
lean_inc_ref(v_a_1150_);
v___x_1972_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1971_, v___f_1970_, v_a_1150_);
if (lean_obj_tag(v___x_1972_) == 0)
{
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_dec_ref(v_a_1150_);
return v___x_1972_;
}
else
{
lean_object* v_pos_1973_; 
v_pos_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_pos_1973_);
v___y_1952_ = v___x_1972_;
v_pos_1953_ = v_pos_1973_;
goto v___jp_1951_;
}
}
else
{
lean_object* v_err_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_err_1974_ = lean_ctor_get(v___x_1972_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v___x_1972_, 0);
lean_dec(v_unused_1982_);
v___x_1976_ = v___x_1972_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_err_1974_);
lean_dec(v___x_1972_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
lean_inc_ref(v_a_1150_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v_a_1150_);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1150_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_err_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_inc_ref(v_a_1150_);
v___y_1952_ = v___x_1979_;
v_pos_1953_ = v_a_1150_;
goto v___jp_1951_;
}
}
}
v___jp_1172_:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_nat_dec_eq(v_idx_1173_, v_idx_1176_);
lean_dec(v_idx_1176_);
lean_dec(v_idx_1173_);
if (v___x_1177_ == 0)
{
lean_dec_ref(v_pos_1175_);
return v___y_1174_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_snd_1181_; lean_object* v_snd_1182_; uint8_t v___x_1183_; 
lean_dec_ref(v___y_1174_);
v___x_1178_ = lean_unsigned_to_nat(64u);
v___x_1179_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pos_1175_);
v___x_1180_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1171_, v___x_1178_, v___x_1179_, v_pos_1175_);
v_snd_1181_ = lean_ctor_get(v___x_1180_, 1);
lean_inc(v_snd_1181_);
v_snd_1182_ = lean_ctor_get(v_snd_1181_, 1);
v___x_1183_ = lean_unbox(v_snd_1182_);
if (v___x_1183_ == 0)
{
lean_object* v_fst_1184_; lean_object* v_fst_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1198_; 
v_fst_1184_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_fst_1184_);
lean_dec_ref(v___x_1180_);
v_fst_1185_ = lean_ctor_get(v_snd_1181_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_snd_1181_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_snd_1181_, 1);
lean_dec(v_unused_1199_);
v___x_1187_ = v_snd_1181_;
v_isShared_1188_ = v_isSharedCheck_1198_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_fst_1185_);
lean_dec(v_snd_1181_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1198_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_nat_dec_eq(v_fst_1184_, v___x_1179_);
lean_dec(v_fst_1184_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
lean_dec_ref(v_pos_1175_);
v___x_1190_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21));
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 1);
lean_ctor_set(v___x_1187_, 1, v___x_1190_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_fst_1185_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_dec(v_fst_1185_);
v___x_1194_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 1);
lean_ctor_set(v___x_1187_, 1, v___x_1194_);
lean_ctor_set(v___x_1187_, 0, v_pos_1175_);
v___x_1196_ = v___x_1187_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_pos_1175_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_fst_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v___x_1180_);
lean_dec_ref(v_pos_1175_);
v_fst_1200_ = lean_ctor_get(v_snd_1181_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_snd_1181_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_snd_1181_, 1);
lean_dec(v_unused_1209_);
v___x_1202_ = v_snd_1181_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_fst_1200_);
lean_dec(v_snd_1181_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_box(0);
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 1);
lean_ctor_set(v___x_1202_, 1, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_fst_1200_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
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
v___jp_1210_:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_nat_dec_eq(v_idx_1211_, v_idx_1214_);
lean_dec(v_idx_1211_);
if (v___x_1215_ == 0)
{
lean_dec(v_idx_1214_);
lean_dec_ref(v_pos_1213_);
return v___y_1212_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v___y_1212_);
v___x_1216_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24);
lean_inc_ref(v_pos_1213_);
v___x_1217_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1216_, v___f_1170_, v_pos_1213_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_dec_ref(v_pos_1213_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_dec(v_idx_1214_);
return v___x_1217_;
}
else
{
lean_object* v_pos_1218_; lean_object* v_idx_1219_; 
v_pos_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_pos_1218_);
v_idx_1219_ = lean_ctor_get(v_pos_1218_, 1);
lean_inc(v_idx_1219_);
v_idx_1173_ = v_idx_1214_;
v___y_1174_ = v___x_1217_;
v_pos_1175_ = v_pos_1218_;
v_idx_1176_ = v_idx_1219_;
goto v___jp_1172_;
}
}
else
{
lean_object* v_err_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_err_1220_ = lean_ctor_get(v___x_1217_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1228_);
v___x_1222_ = v___x_1217_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_err_1220_);
lean_dec(v___x_1217_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
lean_inc_ref(v_pos_1213_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v_pos_1213_);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_pos_1213_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_err_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_inc(v_idx_1214_);
v_idx_1173_ = v_idx_1214_;
v___y_1174_ = v___x_1225_;
v_pos_1175_ = v_pos_1213_;
v_idx_1176_ = v_idx_1214_;
goto v___jp_1172_;
}
}
}
}
}
v___jp_1230_:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_eq(v_idx_1231_, v_idx_1234_);
lean_dec(v_idx_1231_);
if (v___x_1235_ == 0)
{
lean_dec(v_idx_1234_);
lean_dec_ref(v_pos_1233_);
return v___y_1232_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec_ref(v___y_1232_);
v___x_1236_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28);
lean_inc_ref(v_pos_1233_);
v___x_1237_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1236_, v___f_1229_, v_pos_1233_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_dec_ref(v_pos_1233_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_dec(v_idx_1234_);
return v___x_1237_;
}
else
{
lean_object* v_pos_1238_; lean_object* v_idx_1239_; 
v_pos_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_pos_1238_);
v_idx_1239_ = lean_ctor_get(v_pos_1238_, 1);
lean_inc(v_idx_1239_);
v_idx_1211_ = v_idx_1234_;
v___y_1212_ = v___x_1237_;
v_pos_1213_ = v_pos_1238_;
v_idx_1214_ = v_idx_1239_;
goto v___jp_1210_;
}
}
else
{
lean_object* v_err_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_err_1240_ = lean_ctor_get(v___x_1237_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1237_, 0);
lean_dec(v_unused_1248_);
v___x_1242_ = v___x_1237_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_err_1240_);
lean_dec(v___x_1237_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
lean_inc_ref(v_pos_1233_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v_pos_1233_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_pos_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_err_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_inc(v_idx_1234_);
v_idx_1211_ = v_idx_1234_;
v___y_1212_ = v___x_1245_;
v_pos_1213_ = v_pos_1233_;
v_idx_1214_ = v_idx_1234_;
goto v___jp_1210_;
}
}
}
}
}
v___jp_1249_:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_nat_dec_eq(v_idx_1250_, v_idx_1253_);
lean_dec(v_idx_1250_);
if (v___x_1254_ == 0)
{
lean_dec(v_idx_1253_);
lean_dec_ref(v_pos_1252_);
return v___y_1251_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec_ref(v___y_1251_);
v___x_1255_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31);
lean_inc_ref(v_pos_1252_);
v___x_1256_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1255_, v___f_1169_, v_pos_1252_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_dec_ref(v_pos_1252_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_dec(v_idx_1253_);
return v___x_1256_;
}
else
{
lean_object* v_pos_1257_; lean_object* v_idx_1258_; 
v_pos_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_pos_1257_);
v_idx_1258_ = lean_ctor_get(v_pos_1257_, 1);
lean_inc(v_idx_1258_);
v_idx_1231_ = v_idx_1253_;
v___y_1232_ = v___x_1256_;
v_pos_1233_ = v_pos_1257_;
v_idx_1234_ = v_idx_1258_;
goto v___jp_1230_;
}
}
else
{
lean_object* v_err_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_err_1259_ = lean_ctor_get(v___x_1256_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1256_, 0);
lean_dec(v_unused_1267_);
v___x_1261_ = v___x_1256_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_err_1259_);
lean_dec(v___x_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
lean_inc_ref(v_pos_1252_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_pos_1252_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_pos_1252_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_err_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_inc(v_idx_1253_);
v_idx_1231_ = v_idx_1253_;
v___y_1232_ = v___x_1264_;
v_pos_1233_ = v_pos_1252_;
v_idx_1234_ = v_idx_1253_;
goto v___jp_1230_;
}
}
}
}
}
v___jp_1269_:
{
uint8_t v___x_1274_; 
v___x_1274_ = lean_nat_dec_eq(v_idx_1270_, v_idx_1273_);
lean_dec(v_idx_1270_);
if (v___x_1274_ == 0)
{
lean_dec(v_idx_1273_);
lean_dec_ref(v_pos_1272_);
return v___y_1271_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v___y_1271_);
v___x_1275_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35);
lean_inc_ref(v_pos_1272_);
v___x_1276_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1275_, v___f_1268_, v_pos_1272_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_dec_ref(v_pos_1272_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_dec(v_idx_1273_);
return v___x_1276_;
}
else
{
lean_object* v_pos_1277_; lean_object* v_idx_1278_; 
v_pos_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_pos_1277_);
v_idx_1278_ = lean_ctor_get(v_pos_1277_, 1);
lean_inc(v_idx_1278_);
v_idx_1250_ = v_idx_1273_;
v___y_1251_ = v___x_1276_;
v_pos_1252_ = v_pos_1277_;
v_idx_1253_ = v_idx_1278_;
goto v___jp_1249_;
}
}
else
{
lean_object* v_err_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
v_err_1279_ = lean_ctor_get(v___x_1276_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1276_, 0);
lean_dec(v_unused_1287_);
v___x_1281_ = v___x_1276_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_err_1279_);
lean_dec(v___x_1276_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
lean_inc_ref(v_pos_1272_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_pos_1272_);
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_pos_1272_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_err_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_inc(v_idx_1273_);
v_idx_1250_ = v_idx_1273_;
v___y_1251_ = v___x_1284_;
v_pos_1252_ = v_pos_1272_;
v_idx_1253_ = v_idx_1273_;
goto v___jp_1249_;
}
}
}
}
}
v___jp_1288_:
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_nat_dec_eq(v_idx_1289_, v_idx_1292_);
lean_dec(v_idx_1289_);
if (v___x_1293_ == 0)
{
lean_dec(v_idx_1292_);
lean_dec_ref(v_pos_1291_);
return v___y_1290_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v___y_1290_);
v___x_1294_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38);
lean_inc_ref(v_pos_1291_);
v___x_1295_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1294_, v___f_1168_, v_pos_1291_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_dec_ref(v_pos_1291_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_dec(v_idx_1292_);
return v___x_1295_;
}
else
{
lean_object* v_pos_1296_; lean_object* v_idx_1297_; 
v_pos_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_pos_1296_);
v_idx_1297_ = lean_ctor_get(v_pos_1296_, 1);
lean_inc(v_idx_1297_);
v_idx_1270_ = v_idx_1292_;
v___y_1271_ = v___x_1295_;
v_pos_1272_ = v_pos_1296_;
v_idx_1273_ = v_idx_1297_;
goto v___jp_1269_;
}
}
else
{
lean_object* v_err_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
v_err_1298_ = lean_ctor_get(v___x_1295_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v___x_1295_, 0);
lean_dec(v_unused_1306_);
v___x_1300_ = v___x_1295_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_err_1298_);
lean_dec(v___x_1295_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
lean_inc_ref(v_pos_1291_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v_pos_1291_);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_pos_1291_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_err_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_inc(v_idx_1292_);
v_idx_1270_ = v_idx_1292_;
v___y_1271_ = v___x_1303_;
v_pos_1272_ = v_pos_1291_;
v_idx_1273_ = v_idx_1292_;
goto v___jp_1269_;
}
}
}
}
}
v___jp_1308_:
{
uint8_t v___x_1313_; 
v___x_1313_ = lean_nat_dec_eq(v_idx_1309_, v_idx_1312_);
lean_dec(v_idx_1309_);
if (v___x_1313_ == 0)
{
lean_dec(v_idx_1312_);
lean_dec_ref(v_pos_1311_);
return v___y_1310_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec_ref(v___y_1310_);
v___x_1314_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42);
lean_inc_ref(v_pos_1311_);
v___x_1315_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1314_, v___f_1307_, v_pos_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_dec_ref(v_pos_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_dec(v_idx_1312_);
return v___x_1315_;
}
else
{
lean_object* v_pos_1316_; lean_object* v_idx_1317_; 
v_pos_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_pos_1316_);
v_idx_1317_ = lean_ctor_get(v_pos_1316_, 1);
lean_inc(v_idx_1317_);
v_idx_1289_ = v_idx_1312_;
v___y_1290_ = v___x_1315_;
v_pos_1291_ = v_pos_1316_;
v_idx_1292_ = v_idx_1317_;
goto v___jp_1288_;
}
}
else
{
lean_object* v_err_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_err_1318_ = lean_ctor_get(v___x_1315_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v___x_1315_, 0);
lean_dec(v_unused_1326_);
v___x_1320_ = v___x_1315_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_err_1318_);
lean_dec(v___x_1315_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
lean_inc_ref(v_pos_1311_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v_pos_1311_);
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_pos_1311_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_err_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_inc(v_idx_1312_);
v_idx_1289_ = v_idx_1312_;
v___y_1290_ = v___x_1323_;
v_pos_1291_ = v_pos_1311_;
v_idx_1292_ = v_idx_1312_;
goto v___jp_1288_;
}
}
}
}
}
v___jp_1327_:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_nat_dec_eq(v_idx_1328_, v_idx_1331_);
lean_dec(v_idx_1328_);
if (v___x_1332_ == 0)
{
lean_dec(v_idx_1331_);
lean_dec_ref(v_pos_1330_);
return v___y_1329_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v___y_1329_);
v___x_1333_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45);
lean_inc_ref(v_pos_1330_);
v___x_1334_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1333_, v___f_1167_, v_pos_1330_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_dec_ref(v_pos_1330_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_dec(v_idx_1331_);
return v___x_1334_;
}
else
{
lean_object* v_pos_1335_; lean_object* v_idx_1336_; 
v_pos_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_pos_1335_);
v_idx_1336_ = lean_ctor_get(v_pos_1335_, 1);
lean_inc(v_idx_1336_);
v_idx_1309_ = v_idx_1331_;
v___y_1310_ = v___x_1334_;
v_pos_1311_ = v_pos_1335_;
v_idx_1312_ = v_idx_1336_;
goto v___jp_1308_;
}
}
else
{
lean_object* v_err_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_err_1337_ = lean_ctor_get(v___x_1334_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v___x_1334_, 0);
lean_dec(v_unused_1345_);
v___x_1339_ = v___x_1334_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_err_1337_);
lean_dec(v___x_1334_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
lean_inc_ref(v_pos_1330_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_pos_1330_);
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_pos_1330_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_err_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_inc(v_idx_1331_);
v_idx_1309_ = v_idx_1331_;
v___y_1310_ = v___x_1342_;
v_pos_1311_ = v_pos_1330_;
v_idx_1312_ = v_idx_1331_;
goto v___jp_1308_;
}
}
}
}
}
v___jp_1347_:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_nat_dec_eq(v_idx_1348_, v_idx_1351_);
lean_dec(v_idx_1348_);
if (v___x_1352_ == 0)
{
lean_dec(v_idx_1351_);
lean_dec_ref(v_pos_1350_);
return v___y_1349_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref(v___y_1349_);
v___x_1353_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49);
lean_inc_ref(v_pos_1350_);
v___x_1354_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1353_, v___f_1346_, v_pos_1350_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_dec_ref(v_pos_1350_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_dec(v_idx_1351_);
return v___x_1354_;
}
else
{
lean_object* v_pos_1355_; lean_object* v_idx_1356_; 
v_pos_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_pos_1355_);
v_idx_1356_ = lean_ctor_get(v_pos_1355_, 1);
lean_inc(v_idx_1356_);
v_idx_1328_ = v_idx_1351_;
v___y_1329_ = v___x_1354_;
v_pos_1330_ = v_pos_1355_;
v_idx_1331_ = v_idx_1356_;
goto v___jp_1327_;
}
}
else
{
lean_object* v_err_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_err_1357_ = lean_ctor_get(v___x_1354_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v___x_1354_, 0);
lean_dec(v_unused_1365_);
v___x_1359_ = v___x_1354_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_err_1357_);
lean_dec(v___x_1354_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
lean_inc_ref(v_pos_1350_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v_pos_1350_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_pos_1350_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_err_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_inc(v_idx_1351_);
v_idx_1328_ = v_idx_1351_;
v___y_1329_ = v___x_1362_;
v_pos_1330_ = v_pos_1350_;
v_idx_1331_ = v_idx_1351_;
goto v___jp_1327_;
}
}
}
}
}
v___jp_1366_:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_nat_dec_eq(v_idx_1367_, v_idx_1370_);
lean_dec(v_idx_1367_);
if (v___x_1371_ == 0)
{
lean_dec(v_idx_1370_);
lean_dec_ref(v_pos_1369_);
return v___y_1368_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v___y_1368_);
v___x_1372_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52);
lean_inc_ref(v_pos_1369_);
v___x_1373_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1372_, v___f_1166_, v_pos_1369_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_dec_ref(v_pos_1369_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_dec(v_idx_1370_);
return v___x_1373_;
}
else
{
lean_object* v_pos_1374_; lean_object* v_idx_1375_; 
v_pos_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_pos_1374_);
v_idx_1375_ = lean_ctor_get(v_pos_1374_, 1);
lean_inc(v_idx_1375_);
v_idx_1348_ = v_idx_1370_;
v___y_1349_ = v___x_1373_;
v_pos_1350_ = v_pos_1374_;
v_idx_1351_ = v_idx_1375_;
goto v___jp_1347_;
}
}
else
{
lean_object* v_err_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_err_1376_ = lean_ctor_get(v___x_1373_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; 
v_unused_1384_ = lean_ctor_get(v___x_1373_, 0);
lean_dec(v_unused_1384_);
v___x_1378_ = v___x_1373_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_err_1376_);
lean_dec(v___x_1373_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
lean_inc_ref(v_pos_1369_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_pos_1369_);
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_pos_1369_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_err_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_inc(v_idx_1370_);
v_idx_1348_ = v_idx_1370_;
v___y_1349_ = v___x_1381_;
v_pos_1350_ = v_pos_1369_;
v_idx_1351_ = v_idx_1370_;
goto v___jp_1347_;
}
}
}
}
}
v___jp_1386_:
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_nat_dec_eq(v_idx_1387_, v_idx_1390_);
lean_dec(v_idx_1387_);
if (v___x_1391_ == 0)
{
lean_dec(v_idx_1390_);
lean_dec_ref(v_pos_1389_);
return v___y_1388_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v___y_1388_);
v___x_1392_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56);
lean_inc_ref(v_pos_1389_);
v___x_1393_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1392_, v___f_1385_, v_pos_1389_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_dec_ref(v_pos_1389_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_dec(v_idx_1390_);
return v___x_1393_;
}
else
{
lean_object* v_pos_1394_; lean_object* v_idx_1395_; 
v_pos_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_pos_1394_);
v_idx_1395_ = lean_ctor_get(v_pos_1394_, 1);
lean_inc(v_idx_1395_);
v_idx_1367_ = v_idx_1390_;
v___y_1368_ = v___x_1393_;
v_pos_1369_ = v_pos_1394_;
v_idx_1370_ = v_idx_1395_;
goto v___jp_1366_;
}
}
else
{
lean_object* v_err_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_err_1396_ = lean_ctor_get(v___x_1393_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1404_);
v___x_1398_ = v___x_1393_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_err_1396_);
lean_dec(v___x_1393_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
lean_inc_ref(v_pos_1389_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_pos_1389_);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_pos_1389_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_err_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_inc(v_idx_1390_);
v_idx_1367_ = v_idx_1390_;
v___y_1368_ = v___x_1401_;
v_pos_1369_ = v_pos_1389_;
v_idx_1370_ = v_idx_1390_;
goto v___jp_1366_;
}
}
}
}
}
v___jp_1405_:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_nat_dec_eq(v_idx_1406_, v_idx_1409_);
lean_dec(v_idx_1406_);
if (v___x_1410_ == 0)
{
lean_dec(v_idx_1409_);
lean_dec_ref(v_pos_1408_);
return v___y_1407_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v___y_1407_);
v___x_1411_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59);
lean_inc_ref(v_pos_1408_);
v___x_1412_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1411_, v___f_1165_, v_pos_1408_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_dec_ref(v_pos_1408_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_dec(v_idx_1409_);
return v___x_1412_;
}
else
{
lean_object* v_pos_1413_; lean_object* v_idx_1414_; 
v_pos_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_pos_1413_);
v_idx_1414_ = lean_ctor_get(v_pos_1413_, 1);
lean_inc(v_idx_1414_);
v_idx_1387_ = v_idx_1409_;
v___y_1388_ = v___x_1412_;
v_pos_1389_ = v_pos_1413_;
v_idx_1390_ = v_idx_1414_;
goto v___jp_1386_;
}
}
else
{
lean_object* v_err_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
v_err_1415_ = lean_ctor_get(v___x_1412_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v___x_1412_, 0);
lean_dec(v_unused_1423_);
v___x_1417_ = v___x_1412_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_err_1415_);
lean_dec(v___x_1412_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
lean_inc_ref(v_pos_1408_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v_pos_1408_);
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_pos_1408_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_err_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_inc(v_idx_1409_);
v_idx_1387_ = v_idx_1409_;
v___y_1388_ = v___x_1420_;
v_pos_1389_ = v_pos_1408_;
v_idx_1390_ = v_idx_1409_;
goto v___jp_1386_;
}
}
}
}
}
v___jp_1425_:
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_nat_dec_eq(v_idx_1426_, v_idx_1429_);
lean_dec(v_idx_1426_);
if (v___x_1430_ == 0)
{
lean_dec(v_idx_1429_);
lean_dec_ref(v_pos_1428_);
return v___y_1427_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v___y_1427_);
v___x_1431_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63);
lean_inc_ref(v_pos_1428_);
v___x_1432_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1431_, v___f_1424_, v_pos_1428_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec_ref(v_pos_1428_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec(v_idx_1429_);
return v___x_1432_;
}
else
{
lean_object* v_pos_1433_; lean_object* v_idx_1434_; 
v_pos_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_pos_1433_);
v_idx_1434_ = lean_ctor_get(v_pos_1433_, 1);
lean_inc(v_idx_1434_);
v_idx_1406_ = v_idx_1429_;
v___y_1407_ = v___x_1432_;
v_pos_1408_ = v_pos_1433_;
v_idx_1409_ = v_idx_1434_;
goto v___jp_1405_;
}
}
else
{
lean_object* v_err_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_err_1435_ = lean_ctor_get(v___x_1432_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v___x_1432_, 0);
lean_dec(v_unused_1443_);
v___x_1437_ = v___x_1432_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_err_1435_);
lean_dec(v___x_1432_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
lean_inc_ref(v_pos_1428_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v_pos_1428_);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_pos_1428_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_err_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_inc(v_idx_1429_);
v_idx_1406_ = v_idx_1429_;
v___y_1407_ = v___x_1440_;
v_pos_1408_ = v_pos_1428_;
v_idx_1409_ = v_idx_1429_;
goto v___jp_1405_;
}
}
}
}
}
v___jp_1444_:
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_nat_dec_eq(v_idx_1445_, v_idx_1448_);
lean_dec(v_idx_1445_);
if (v___x_1449_ == 0)
{
lean_dec(v_idx_1448_);
lean_dec_ref(v_pos_1447_);
return v___y_1446_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec_ref(v___y_1446_);
v___x_1450_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66);
lean_inc_ref(v_pos_1447_);
v___x_1451_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1450_, v___f_1164_, v_pos_1447_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_dec_ref(v_pos_1447_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_dec(v_idx_1448_);
return v___x_1451_;
}
else
{
lean_object* v_pos_1452_; lean_object* v_idx_1453_; 
v_pos_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_pos_1452_);
v_idx_1453_ = lean_ctor_get(v_pos_1452_, 1);
lean_inc(v_idx_1453_);
v_idx_1426_ = v_idx_1448_;
v___y_1427_ = v___x_1451_;
v_pos_1428_ = v_pos_1452_;
v_idx_1429_ = v_idx_1453_;
goto v___jp_1425_;
}
}
else
{
lean_object* v_err_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_err_1454_ = lean_ctor_get(v___x_1451_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v___x_1451_, 0);
lean_dec(v_unused_1462_);
v___x_1456_ = v___x_1451_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_err_1454_);
lean_dec(v___x_1451_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
lean_inc_ref(v_pos_1447_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v_pos_1447_);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_pos_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_err_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_inc(v_idx_1448_);
v_idx_1426_ = v_idx_1448_;
v___y_1427_ = v___x_1459_;
v_pos_1428_ = v_pos_1447_;
v_idx_1429_ = v_idx_1448_;
goto v___jp_1425_;
}
}
}
}
}
v___jp_1464_:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_nat_dec_eq(v_idx_1465_, v_idx_1468_);
lean_dec(v_idx_1465_);
if (v___x_1469_ == 0)
{
lean_dec(v_idx_1468_);
lean_dec_ref(v_pos_1467_);
return v___y_1466_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v___y_1466_);
v___x_1470_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70);
lean_inc_ref(v_pos_1467_);
v___x_1471_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1470_, v___f_1463_, v_pos_1467_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_dec_ref(v_pos_1467_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_dec(v_idx_1468_);
return v___x_1471_;
}
else
{
lean_object* v_pos_1472_; lean_object* v_idx_1473_; 
v_pos_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_pos_1472_);
v_idx_1473_ = lean_ctor_get(v_pos_1472_, 1);
lean_inc(v_idx_1473_);
v_idx_1445_ = v_idx_1468_;
v___y_1446_ = v___x_1471_;
v_pos_1447_ = v_pos_1472_;
v_idx_1448_ = v_idx_1473_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_err_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_err_1474_ = lean_ctor_get(v___x_1471_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v___x_1471_, 0);
lean_dec(v_unused_1482_);
v___x_1476_ = v___x_1471_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_err_1474_);
lean_dec(v___x_1471_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
lean_inc_ref(v_pos_1467_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v_pos_1467_);
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_pos_1467_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_err_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_inc(v_idx_1468_);
v_idx_1445_ = v_idx_1468_;
v___y_1446_ = v___x_1479_;
v_pos_1447_ = v_pos_1467_;
v_idx_1448_ = v_idx_1468_;
goto v___jp_1444_;
}
}
}
}
}
v___jp_1483_:
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_nat_dec_eq(v_idx_1484_, v_idx_1487_);
lean_dec(v_idx_1484_);
if (v___x_1488_ == 0)
{
lean_dec(v_idx_1487_);
lean_dec_ref(v_pos_1486_);
return v___y_1485_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref(v___y_1485_);
v___x_1489_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73);
lean_inc_ref(v_pos_1486_);
v___x_1490_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1489_, v___f_1163_, v_pos_1486_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_dec_ref(v_pos_1486_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_dec(v_idx_1487_);
return v___x_1490_;
}
else
{
lean_object* v_pos_1491_; lean_object* v_idx_1492_; 
v_pos_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_pos_1491_);
v_idx_1492_ = lean_ctor_get(v_pos_1491_, 1);
lean_inc(v_idx_1492_);
v_idx_1465_ = v_idx_1487_;
v___y_1466_ = v___x_1490_;
v_pos_1467_ = v_pos_1491_;
v_idx_1468_ = v_idx_1492_;
goto v___jp_1464_;
}
}
else
{
lean_object* v_err_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_err_1493_ = lean_ctor_get(v___x_1490_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v___x_1490_, 0);
lean_dec(v_unused_1501_);
v___x_1495_ = v___x_1490_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_err_1493_);
lean_dec(v___x_1490_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
lean_inc_ref(v_pos_1486_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v_pos_1486_);
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_pos_1486_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_err_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_inc(v_idx_1487_);
v_idx_1465_ = v_idx_1487_;
v___y_1466_ = v___x_1498_;
v_pos_1467_ = v_pos_1486_;
v_idx_1468_ = v_idx_1487_;
goto v___jp_1464_;
}
}
}
}
}
v___jp_1503_:
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_nat_dec_eq(v_idx_1504_, v_idx_1507_);
lean_dec(v_idx_1504_);
if (v___x_1508_ == 0)
{
lean_dec(v_idx_1507_);
lean_dec_ref(v_pos_1506_);
return v___y_1505_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec_ref(v___y_1505_);
v___x_1509_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77);
lean_inc_ref(v_pos_1506_);
v___x_1510_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1509_, v___f_1502_, v_pos_1506_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec_ref(v_pos_1506_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec(v_idx_1507_);
return v___x_1510_;
}
else
{
lean_object* v_pos_1511_; lean_object* v_idx_1512_; 
v_pos_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_pos_1511_);
v_idx_1512_ = lean_ctor_get(v_pos_1511_, 1);
lean_inc(v_idx_1512_);
v_idx_1484_ = v_idx_1507_;
v___y_1485_ = v___x_1510_;
v_pos_1486_ = v_pos_1511_;
v_idx_1487_ = v_idx_1512_;
goto v___jp_1483_;
}
}
else
{
lean_object* v_err_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_err_1513_ = lean_ctor_get(v___x_1510_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v___x_1510_, 0);
lean_dec(v_unused_1521_);
v___x_1515_ = v___x_1510_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_err_1513_);
lean_dec(v___x_1510_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
lean_inc_ref(v_pos_1506_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v_pos_1506_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_pos_1506_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_err_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_inc(v_idx_1507_);
v_idx_1484_ = v_idx_1507_;
v___y_1485_ = v___x_1518_;
v_pos_1486_ = v_pos_1506_;
v_idx_1487_ = v_idx_1507_;
goto v___jp_1483_;
}
}
}
}
}
v___jp_1522_:
{
uint8_t v___x_1527_; 
v___x_1527_ = lean_nat_dec_eq(v_idx_1523_, v_idx_1526_);
lean_dec(v_idx_1523_);
if (v___x_1527_ == 0)
{
lean_dec(v_idx_1526_);
lean_dec_ref(v_pos_1525_);
return v___y_1524_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec_ref(v___y_1524_);
v___x_1528_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80);
lean_inc_ref(v_pos_1525_);
v___x_1529_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1528_, v___f_1162_, v_pos_1525_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_dec_ref(v_pos_1525_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_dec(v_idx_1526_);
return v___x_1529_;
}
else
{
lean_object* v_pos_1530_; lean_object* v_idx_1531_; 
v_pos_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_pos_1530_);
v_idx_1531_ = lean_ctor_get(v_pos_1530_, 1);
lean_inc(v_idx_1531_);
v_idx_1504_ = v_idx_1526_;
v___y_1505_ = v___x_1529_;
v_pos_1506_ = v_pos_1530_;
v_idx_1507_ = v_idx_1531_;
goto v___jp_1503_;
}
}
else
{
lean_object* v_err_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_err_1532_ = lean_ctor_get(v___x_1529_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v___x_1529_, 0);
lean_dec(v_unused_1540_);
v___x_1534_ = v___x_1529_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_err_1532_);
lean_dec(v___x_1529_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
lean_inc_ref(v_pos_1525_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v_pos_1525_);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_pos_1525_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_err_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_inc(v_idx_1526_);
v_idx_1504_ = v_idx_1526_;
v___y_1505_ = v___x_1537_;
v_pos_1506_ = v_pos_1525_;
v_idx_1507_ = v_idx_1526_;
goto v___jp_1503_;
}
}
}
}
}
v___jp_1542_:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_nat_dec_eq(v_idx_1543_, v_idx_1546_);
lean_dec(v_idx_1543_);
if (v___x_1547_ == 0)
{
lean_dec(v_idx_1546_);
lean_dec_ref(v_pos_1545_);
return v___y_1544_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref(v___y_1544_);
v___x_1548_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84);
lean_inc_ref(v_pos_1545_);
v___x_1549_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1548_, v___f_1541_, v_pos_1545_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_dec_ref(v_pos_1545_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_dec(v_idx_1546_);
return v___x_1549_;
}
else
{
lean_object* v_pos_1550_; lean_object* v_idx_1551_; 
v_pos_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_pos_1550_);
v_idx_1551_ = lean_ctor_get(v_pos_1550_, 1);
lean_inc(v_idx_1551_);
v_idx_1523_ = v_idx_1546_;
v___y_1524_ = v___x_1549_;
v_pos_1525_ = v_pos_1550_;
v_idx_1526_ = v_idx_1551_;
goto v___jp_1522_;
}
}
else
{
lean_object* v_err_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_err_1552_ = lean_ctor_get(v___x_1549_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v___x_1549_, 0);
lean_dec(v_unused_1560_);
v___x_1554_ = v___x_1549_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_err_1552_);
lean_dec(v___x_1549_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
lean_inc_ref(v_pos_1545_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v_pos_1545_);
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_pos_1545_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_err_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_inc(v_idx_1546_);
v_idx_1523_ = v_idx_1546_;
v___y_1524_ = v___x_1557_;
v_pos_1525_ = v_pos_1545_;
v_idx_1526_ = v_idx_1546_;
goto v___jp_1522_;
}
}
}
}
}
v___jp_1561_:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_nat_dec_eq(v_idx_1562_, v_idx_1565_);
lean_dec(v_idx_1562_);
if (v___x_1566_ == 0)
{
lean_dec(v_idx_1565_);
lean_dec_ref(v_pos_1564_);
return v___y_1563_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref(v___y_1563_);
v___x_1567_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87);
lean_inc_ref(v_pos_1564_);
v___x_1568_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1567_, v___f_1161_, v_pos_1564_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_dec_ref(v_pos_1564_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_dec(v_idx_1565_);
return v___x_1568_;
}
else
{
lean_object* v_pos_1569_; lean_object* v_idx_1570_; 
v_pos_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_pos_1569_);
v_idx_1570_ = lean_ctor_get(v_pos_1569_, 1);
lean_inc(v_idx_1570_);
v_idx_1543_ = v_idx_1565_;
v___y_1544_ = v___x_1568_;
v_pos_1545_ = v_pos_1569_;
v_idx_1546_ = v_idx_1570_;
goto v___jp_1542_;
}
}
else
{
lean_object* v_err_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
v_err_1571_ = lean_ctor_get(v___x_1568_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v___x_1568_, 0);
lean_dec(v_unused_1579_);
v___x_1573_ = v___x_1568_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_err_1571_);
lean_dec(v___x_1568_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
lean_inc_ref(v_pos_1564_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_pos_1564_);
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_pos_1564_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_err_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_inc(v_idx_1565_);
v_idx_1543_ = v_idx_1565_;
v___y_1544_ = v___x_1576_;
v_pos_1545_ = v_pos_1564_;
v_idx_1546_ = v_idx_1565_;
goto v___jp_1542_;
}
}
}
}
}
v___jp_1581_:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_nat_dec_eq(v_idx_1582_, v_idx_1585_);
lean_dec(v_idx_1582_);
if (v___x_1586_ == 0)
{
lean_dec(v_idx_1585_);
lean_dec_ref(v_pos_1584_);
return v___y_1583_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec_ref(v___y_1583_);
v___x_1587_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91);
lean_inc_ref(v_pos_1584_);
v___x_1588_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1587_, v___f_1580_, v_pos_1584_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_dec_ref(v_pos_1584_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_dec(v_idx_1585_);
return v___x_1588_;
}
else
{
lean_object* v_pos_1589_; lean_object* v_idx_1590_; 
v_pos_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_pos_1589_);
v_idx_1590_ = lean_ctor_get(v_pos_1589_, 1);
lean_inc(v_idx_1590_);
v_idx_1562_ = v_idx_1585_;
v___y_1563_ = v___x_1588_;
v_pos_1564_ = v_pos_1589_;
v_idx_1565_ = v_idx_1590_;
goto v___jp_1561_;
}
}
else
{
lean_object* v_err_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_err_1591_ = lean_ctor_get(v___x_1588_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v___x_1588_, 0);
lean_dec(v_unused_1599_);
v___x_1593_ = v___x_1588_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_err_1591_);
lean_dec(v___x_1588_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
lean_inc_ref(v_pos_1584_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v_pos_1584_);
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_pos_1584_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_err_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_inc(v_idx_1585_);
v_idx_1562_ = v_idx_1585_;
v___y_1563_ = v___x_1596_;
v_pos_1564_ = v_pos_1584_;
v_idx_1565_ = v_idx_1585_;
goto v___jp_1561_;
}
}
}
}
}
v___jp_1600_:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_nat_dec_eq(v_idx_1601_, v_idx_1604_);
lean_dec(v_idx_1601_);
if (v___x_1605_ == 0)
{
lean_dec(v_idx_1604_);
lean_dec_ref(v_pos_1603_);
return v___y_1602_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v___y_1602_);
v___x_1606_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94);
lean_inc_ref(v_pos_1603_);
v___x_1607_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1606_, v___f_1160_, v_pos_1603_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_dec_ref(v_pos_1603_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_dec(v_idx_1604_);
return v___x_1607_;
}
else
{
lean_object* v_pos_1608_; lean_object* v_idx_1609_; 
v_pos_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_pos_1608_);
v_idx_1609_ = lean_ctor_get(v_pos_1608_, 1);
lean_inc(v_idx_1609_);
v_idx_1582_ = v_idx_1604_;
v___y_1583_ = v___x_1607_;
v_pos_1584_ = v_pos_1608_;
v_idx_1585_ = v_idx_1609_;
goto v___jp_1581_;
}
}
else
{
lean_object* v_err_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_err_1610_ = lean_ctor_get(v___x_1607_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; 
v_unused_1618_ = lean_ctor_get(v___x_1607_, 0);
lean_dec(v_unused_1618_);
v___x_1612_ = v___x_1607_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_err_1610_);
lean_dec(v___x_1607_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
lean_inc_ref(v_pos_1603_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v_pos_1603_);
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_pos_1603_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_err_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_inc(v_idx_1604_);
v_idx_1582_ = v_idx_1604_;
v___y_1583_ = v___x_1615_;
v_pos_1584_ = v_pos_1603_;
v_idx_1585_ = v_idx_1604_;
goto v___jp_1581_;
}
}
}
}
}
v___jp_1620_:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_nat_dec_eq(v_idx_1621_, v_idx_1624_);
lean_dec(v_idx_1621_);
if (v___x_1625_ == 0)
{
lean_dec(v_idx_1624_);
lean_dec_ref(v_pos_1623_);
return v___y_1622_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v___y_1622_);
v___x_1626_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98);
lean_inc_ref(v_pos_1623_);
v___x_1627_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1626_, v___f_1619_, v_pos_1623_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref(v_pos_1623_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec(v_idx_1624_);
return v___x_1627_;
}
else
{
lean_object* v_pos_1628_; lean_object* v_idx_1629_; 
v_pos_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_pos_1628_);
v_idx_1629_ = lean_ctor_get(v_pos_1628_, 1);
lean_inc(v_idx_1629_);
v_idx_1601_ = v_idx_1624_;
v___y_1602_ = v___x_1627_;
v_pos_1603_ = v_pos_1628_;
v_idx_1604_ = v_idx_1629_;
goto v___jp_1600_;
}
}
else
{
lean_object* v_err_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_err_1630_ = lean_ctor_get(v___x_1627_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v___x_1627_, 0);
lean_dec(v_unused_1638_);
v___x_1632_ = v___x_1627_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_err_1630_);
lean_dec(v___x_1627_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
lean_inc_ref(v_pos_1623_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v_pos_1623_);
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_pos_1623_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_err_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_inc(v_idx_1624_);
v_idx_1601_ = v_idx_1624_;
v___y_1602_ = v___x_1635_;
v_pos_1603_ = v_pos_1623_;
v_idx_1604_ = v_idx_1624_;
goto v___jp_1600_;
}
}
}
}
}
v___jp_1639_:
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_nat_dec_eq(v_idx_1640_, v_idx_1643_);
lean_dec(v_idx_1640_);
if (v___x_1644_ == 0)
{
lean_dec(v_idx_1643_);
lean_dec_ref(v_pos_1642_);
return v___y_1641_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec_ref(v___y_1641_);
v___x_1645_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101);
lean_inc_ref(v_pos_1642_);
v___x_1646_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1645_, v___f_1159_, v_pos_1642_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec_ref(v_pos_1642_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec(v_idx_1643_);
return v___x_1646_;
}
else
{
lean_object* v_pos_1647_; lean_object* v_idx_1648_; 
v_pos_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_pos_1647_);
v_idx_1648_ = lean_ctor_get(v_pos_1647_, 1);
lean_inc(v_idx_1648_);
v_idx_1621_ = v_idx_1643_;
v___y_1622_ = v___x_1646_;
v_pos_1623_ = v_pos_1647_;
v_idx_1624_ = v_idx_1648_;
goto v___jp_1620_;
}
}
else
{
lean_object* v_err_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_err_1649_ = lean_ctor_get(v___x_1646_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v___x_1646_, 0);
lean_dec(v_unused_1657_);
v___x_1651_ = v___x_1646_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_err_1649_);
lean_dec(v___x_1646_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
lean_inc_ref(v_pos_1642_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v_pos_1642_);
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_pos_1642_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_err_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_inc(v_idx_1643_);
v_idx_1621_ = v_idx_1643_;
v___y_1622_ = v___x_1654_;
v_pos_1623_ = v_pos_1642_;
v_idx_1624_ = v_idx_1643_;
goto v___jp_1620_;
}
}
}
}
}
v___jp_1659_:
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_nat_dec_eq(v_idx_1660_, v_idx_1663_);
lean_dec(v_idx_1660_);
if (v___x_1664_ == 0)
{
lean_dec(v_idx_1663_);
lean_dec_ref(v_pos_1662_);
return v___y_1661_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec_ref(v___y_1661_);
v___x_1665_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105);
lean_inc_ref(v_pos_1662_);
v___x_1666_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1665_, v___f_1658_, v_pos_1662_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_dec_ref(v_pos_1662_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_dec(v_idx_1663_);
return v___x_1666_;
}
else
{
lean_object* v_pos_1667_; lean_object* v_idx_1668_; 
v_pos_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_pos_1667_);
v_idx_1668_ = lean_ctor_get(v_pos_1667_, 1);
lean_inc(v_idx_1668_);
v_idx_1640_ = v_idx_1663_;
v___y_1641_ = v___x_1666_;
v_pos_1642_ = v_pos_1667_;
v_idx_1643_ = v_idx_1668_;
goto v___jp_1639_;
}
}
else
{
lean_object* v_err_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_err_1669_ = lean_ctor_get(v___x_1666_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v___x_1666_, 0);
lean_dec(v_unused_1677_);
v___x_1671_ = v___x_1666_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_err_1669_);
lean_dec(v___x_1666_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
lean_inc_ref(v_pos_1662_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v_pos_1662_);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_pos_1662_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_err_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_inc(v_idx_1663_);
v_idx_1640_ = v_idx_1663_;
v___y_1641_ = v___x_1674_;
v_pos_1642_ = v_pos_1662_;
v_idx_1643_ = v_idx_1663_;
goto v___jp_1639_;
}
}
}
}
}
v___jp_1678_:
{
uint8_t v___x_1683_; 
v___x_1683_ = lean_nat_dec_eq(v_idx_1679_, v_idx_1682_);
lean_dec(v_idx_1679_);
if (v___x_1683_ == 0)
{
lean_dec(v_idx_1682_);
lean_dec_ref(v_pos_1681_);
return v___y_1680_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v___y_1680_);
v___x_1684_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108);
lean_inc_ref(v_pos_1681_);
v___x_1685_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1684_, v___f_1158_, v_pos_1681_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_dec_ref(v_pos_1681_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_dec(v_idx_1682_);
return v___x_1685_;
}
else
{
lean_object* v_pos_1686_; lean_object* v_idx_1687_; 
v_pos_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_pos_1686_);
v_idx_1687_ = lean_ctor_get(v_pos_1686_, 1);
lean_inc(v_idx_1687_);
v_idx_1660_ = v_idx_1682_;
v___y_1661_ = v___x_1685_;
v_pos_1662_ = v_pos_1686_;
v_idx_1663_ = v_idx_1687_;
goto v___jp_1659_;
}
}
else
{
lean_object* v_err_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_err_1688_ = lean_ctor_get(v___x_1685_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1685_, 0);
lean_dec(v_unused_1696_);
v___x_1690_ = v___x_1685_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_err_1688_);
lean_dec(v___x_1685_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
lean_inc_ref(v_pos_1681_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v_pos_1681_);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_pos_1681_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_err_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_inc(v_idx_1682_);
v_idx_1660_ = v_idx_1682_;
v___y_1661_ = v___x_1693_;
v_pos_1662_ = v_pos_1681_;
v_idx_1663_ = v_idx_1682_;
goto v___jp_1659_;
}
}
}
}
}
v___jp_1698_:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_nat_dec_eq(v_idx_1699_, v_idx_1702_);
lean_dec(v_idx_1699_);
if (v___x_1703_ == 0)
{
lean_dec(v_idx_1702_);
lean_dec_ref(v_pos_1701_);
return v___y_1700_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref(v___y_1700_);
v___x_1704_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112);
lean_inc_ref(v_pos_1701_);
v___x_1705_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1704_, v___f_1697_, v_pos_1701_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec_ref(v_pos_1701_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec(v_idx_1702_);
return v___x_1705_;
}
else
{
lean_object* v_pos_1706_; lean_object* v_idx_1707_; 
v_pos_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_pos_1706_);
v_idx_1707_ = lean_ctor_get(v_pos_1706_, 1);
lean_inc(v_idx_1707_);
v_idx_1679_ = v_idx_1702_;
v___y_1680_ = v___x_1705_;
v_pos_1681_ = v_pos_1706_;
v_idx_1682_ = v_idx_1707_;
goto v___jp_1678_;
}
}
else
{
lean_object* v_err_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_err_1708_ = lean_ctor_get(v___x_1705_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; 
v_unused_1716_ = lean_ctor_get(v___x_1705_, 0);
lean_dec(v_unused_1716_);
v___x_1710_ = v___x_1705_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_err_1708_);
lean_dec(v___x_1705_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
lean_inc_ref(v_pos_1701_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v_pos_1701_);
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_pos_1701_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_err_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_inc(v_idx_1702_);
v_idx_1679_ = v_idx_1702_;
v___y_1680_ = v___x_1713_;
v_pos_1681_ = v_pos_1701_;
v_idx_1682_ = v_idx_1702_;
goto v___jp_1678_;
}
}
}
}
}
v___jp_1717_:
{
uint8_t v___x_1722_; 
v___x_1722_ = lean_nat_dec_eq(v_idx_1718_, v_idx_1721_);
lean_dec(v_idx_1718_);
if (v___x_1722_ == 0)
{
lean_dec(v_idx_1721_);
lean_dec_ref(v_pos_1720_);
return v___y_1719_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec_ref(v___y_1719_);
v___x_1723_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115);
lean_inc_ref(v_pos_1720_);
v___x_1724_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1723_, v___f_1157_, v_pos_1720_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_dec_ref(v_pos_1720_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_dec(v_idx_1721_);
return v___x_1724_;
}
else
{
lean_object* v_pos_1725_; lean_object* v_idx_1726_; 
v_pos_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_pos_1725_);
v_idx_1726_ = lean_ctor_get(v_pos_1725_, 1);
lean_inc(v_idx_1726_);
v_idx_1699_ = v_idx_1721_;
v___y_1700_ = v___x_1724_;
v_pos_1701_ = v_pos_1725_;
v_idx_1702_ = v_idx_1726_;
goto v___jp_1698_;
}
}
else
{
lean_object* v_err_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_err_1727_ = lean_ctor_get(v___x_1724_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v___x_1724_, 0);
lean_dec(v_unused_1735_);
v___x_1729_ = v___x_1724_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_err_1727_);
lean_dec(v___x_1724_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
lean_inc_ref(v_pos_1720_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v_pos_1720_);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_pos_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_err_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_inc(v_idx_1721_);
v_idx_1699_ = v_idx_1721_;
v___y_1700_ = v___x_1732_;
v_pos_1701_ = v_pos_1720_;
v_idx_1702_ = v_idx_1721_;
goto v___jp_1698_;
}
}
}
}
}
v___jp_1737_:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_nat_dec_eq(v_idx_1738_, v_idx_1741_);
lean_dec(v_idx_1738_);
if (v___x_1742_ == 0)
{
lean_dec(v_idx_1741_);
lean_dec_ref(v_pos_1740_);
return v___y_1739_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec_ref(v___y_1739_);
v___x_1743_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119);
lean_inc_ref(v_pos_1740_);
v___x_1744_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1743_, v___f_1736_, v_pos_1740_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_dec_ref(v_pos_1740_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_dec(v_idx_1741_);
return v___x_1744_;
}
else
{
lean_object* v_pos_1745_; lean_object* v_idx_1746_; 
v_pos_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_pos_1745_);
v_idx_1746_ = lean_ctor_get(v_pos_1745_, 1);
lean_inc(v_idx_1746_);
v_idx_1718_ = v_idx_1741_;
v___y_1719_ = v___x_1744_;
v_pos_1720_ = v_pos_1745_;
v_idx_1721_ = v_idx_1746_;
goto v___jp_1717_;
}
}
else
{
lean_object* v_err_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_err_1747_ = lean_ctor_get(v___x_1744_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1744_, 0);
lean_dec(v_unused_1755_);
v___x_1749_ = v___x_1744_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_err_1747_);
lean_dec(v___x_1744_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
lean_inc_ref(v_pos_1740_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v_pos_1740_);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_pos_1740_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_err_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_inc(v_idx_1741_);
v_idx_1718_ = v_idx_1741_;
v___y_1719_ = v___x_1752_;
v_pos_1720_ = v_pos_1740_;
v_idx_1721_ = v_idx_1741_;
goto v___jp_1717_;
}
}
}
}
}
v___jp_1756_:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_nat_dec_eq(v_idx_1757_, v_idx_1760_);
lean_dec(v_idx_1757_);
if (v___x_1761_ == 0)
{
lean_dec(v_idx_1760_);
lean_dec_ref(v_pos_1759_);
return v___y_1758_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec_ref(v___y_1758_);
v___x_1762_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122);
lean_inc_ref(v_pos_1759_);
v___x_1763_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1762_, v___f_1156_, v_pos_1759_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_dec_ref(v_pos_1759_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_dec(v_idx_1760_);
return v___x_1763_;
}
else
{
lean_object* v_pos_1764_; lean_object* v_idx_1765_; 
v_pos_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_pos_1764_);
v_idx_1765_ = lean_ctor_get(v_pos_1764_, 1);
lean_inc(v_idx_1765_);
v_idx_1738_ = v_idx_1760_;
v___y_1739_ = v___x_1763_;
v_pos_1740_ = v_pos_1764_;
v_idx_1741_ = v_idx_1765_;
goto v___jp_1737_;
}
}
else
{
lean_object* v_err_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
v_err_1766_ = lean_ctor_get(v___x_1763_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1763_, 0);
lean_dec(v_unused_1774_);
v___x_1768_ = v___x_1763_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_err_1766_);
lean_dec(v___x_1763_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
lean_inc_ref(v_pos_1759_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v_pos_1759_);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_pos_1759_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_err_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_inc(v_idx_1760_);
v_idx_1738_ = v_idx_1760_;
v___y_1739_ = v___x_1771_;
v_pos_1740_ = v_pos_1759_;
v_idx_1741_ = v_idx_1760_;
goto v___jp_1737_;
}
}
}
}
}
v___jp_1776_:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_nat_dec_eq(v_idx_1777_, v_idx_1780_);
lean_dec(v_idx_1777_);
if (v___x_1781_ == 0)
{
lean_dec(v_idx_1780_);
lean_dec_ref(v_pos_1779_);
return v___y_1778_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec_ref(v___y_1778_);
v___x_1782_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126);
lean_inc_ref(v_pos_1779_);
v___x_1783_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1782_, v___f_1775_, v_pos_1779_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_dec_ref(v_pos_1779_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_dec(v_idx_1780_);
return v___x_1783_;
}
else
{
lean_object* v_pos_1784_; lean_object* v_idx_1785_; 
v_pos_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_pos_1784_);
v_idx_1785_ = lean_ctor_get(v_pos_1784_, 1);
lean_inc(v_idx_1785_);
v_idx_1757_ = v_idx_1780_;
v___y_1758_ = v___x_1783_;
v_pos_1759_ = v_pos_1784_;
v_idx_1760_ = v_idx_1785_;
goto v___jp_1756_;
}
}
else
{
lean_object* v_err_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_err_1786_ = lean_ctor_get(v___x_1783_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v___x_1783_, 0);
lean_dec(v_unused_1794_);
v___x_1788_ = v___x_1783_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_err_1786_);
lean_dec(v___x_1783_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
lean_inc_ref(v_pos_1779_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v_pos_1779_);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_pos_1779_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_err_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_inc(v_idx_1780_);
v_idx_1757_ = v_idx_1780_;
v___y_1758_ = v___x_1791_;
v_pos_1759_ = v_pos_1779_;
v_idx_1760_ = v_idx_1780_;
goto v___jp_1756_;
}
}
}
}
}
v___jp_1795_:
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_eq(v_idx_1796_, v_idx_1799_);
lean_dec(v_idx_1796_);
if (v___x_1800_ == 0)
{
lean_dec(v_idx_1799_);
lean_dec_ref(v_pos_1798_);
return v___y_1797_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref(v___y_1797_);
v___x_1801_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129);
lean_inc_ref(v_pos_1798_);
v___x_1802_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1801_, v___f_1155_, v_pos_1798_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_dec_ref(v_pos_1798_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_dec(v_idx_1799_);
return v___x_1802_;
}
else
{
lean_object* v_pos_1803_; lean_object* v_idx_1804_; 
v_pos_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_pos_1803_);
v_idx_1804_ = lean_ctor_get(v_pos_1803_, 1);
lean_inc(v_idx_1804_);
v_idx_1777_ = v_idx_1799_;
v___y_1778_ = v___x_1802_;
v_pos_1779_ = v_pos_1803_;
v_idx_1780_ = v_idx_1804_;
goto v___jp_1776_;
}
}
else
{
lean_object* v_err_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_err_1805_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v___x_1802_, 0);
lean_dec(v_unused_1813_);
v___x_1807_ = v___x_1802_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_err_1805_);
lean_dec(v___x_1802_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
lean_inc_ref(v_pos_1798_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v_pos_1798_);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_pos_1798_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_err_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_inc(v_idx_1799_);
v_idx_1777_ = v_idx_1799_;
v___y_1778_ = v___x_1810_;
v_pos_1779_ = v_pos_1798_;
v_idx_1780_ = v_idx_1799_;
goto v___jp_1776_;
}
}
}
}
}
v___jp_1815_:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_nat_dec_eq(v_idx_1816_, v_idx_1819_);
lean_dec(v_idx_1816_);
if (v___x_1820_ == 0)
{
lean_dec(v_idx_1819_);
lean_dec_ref(v_pos_1818_);
return v___y_1817_;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v___y_1817_);
v___x_1821_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133);
lean_inc_ref(v_pos_1818_);
v___x_1822_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1821_, v___f_1814_, v_pos_1818_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_dec_ref(v_pos_1818_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_dec(v_idx_1819_);
return v___x_1822_;
}
else
{
lean_object* v_pos_1823_; lean_object* v_idx_1824_; 
v_pos_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_pos_1823_);
v_idx_1824_ = lean_ctor_get(v_pos_1823_, 1);
lean_inc(v_idx_1824_);
v_idx_1796_ = v_idx_1819_;
v___y_1797_ = v___x_1822_;
v_pos_1798_ = v_pos_1823_;
v_idx_1799_ = v_idx_1824_;
goto v___jp_1795_;
}
}
else
{
lean_object* v_err_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_err_1825_ = lean_ctor_get(v___x_1822_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v___x_1822_, 0);
lean_dec(v_unused_1833_);
v___x_1827_ = v___x_1822_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_err_1825_);
lean_dec(v___x_1822_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
lean_inc_ref(v_pos_1818_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v_pos_1818_);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_pos_1818_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_err_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_inc(v_idx_1819_);
v_idx_1796_ = v_idx_1819_;
v___y_1797_ = v___x_1830_;
v_pos_1798_ = v_pos_1818_;
v_idx_1799_ = v_idx_1819_;
goto v___jp_1795_;
}
}
}
}
}
v___jp_1834_:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_nat_dec_eq(v_idx_1835_, v_idx_1838_);
lean_dec(v_idx_1835_);
if (v___x_1839_ == 0)
{
lean_dec(v_idx_1838_);
lean_dec_ref(v_pos_1837_);
return v___y_1836_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec_ref(v___y_1836_);
v___x_1840_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136);
lean_inc_ref(v_pos_1837_);
v___x_1841_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1840_, v___f_1154_, v_pos_1837_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_dec_ref(v_pos_1837_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_dec(v_idx_1838_);
return v___x_1841_;
}
else
{
lean_object* v_pos_1842_; lean_object* v_idx_1843_; 
v_pos_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_pos_1842_);
v_idx_1843_ = lean_ctor_get(v_pos_1842_, 1);
lean_inc(v_idx_1843_);
v_idx_1816_ = v_idx_1838_;
v___y_1817_ = v___x_1841_;
v_pos_1818_ = v_pos_1842_;
v_idx_1819_ = v_idx_1843_;
goto v___jp_1815_;
}
}
else
{
lean_object* v_err_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_err_1844_ = lean_ctor_get(v___x_1841_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1852_);
v___x_1846_ = v___x_1841_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_err_1844_);
lean_dec(v___x_1841_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
lean_inc_ref(v_pos_1837_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v_pos_1837_);
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_pos_1837_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_err_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_inc(v_idx_1838_);
v_idx_1816_ = v_idx_1838_;
v___y_1817_ = v___x_1849_;
v_pos_1818_ = v_pos_1837_;
v_idx_1819_ = v_idx_1838_;
goto v___jp_1815_;
}
}
}
}
}
v___jp_1854_:
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_nat_dec_eq(v_idx_1855_, v_idx_1858_);
lean_dec(v_idx_1855_);
if (v___x_1859_ == 0)
{
lean_dec(v_idx_1858_);
lean_dec_ref(v_pos_1857_);
return v___y_1856_;
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec_ref(v___y_1856_);
v___x_1860_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140);
lean_inc_ref(v_pos_1857_);
v___x_1861_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1860_, v___f_1853_, v_pos_1857_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref(v_pos_1857_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec(v_idx_1858_);
return v___x_1861_;
}
else
{
lean_object* v_pos_1862_; lean_object* v_idx_1863_; 
v_pos_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_pos_1862_);
v_idx_1863_ = lean_ctor_get(v_pos_1862_, 1);
lean_inc(v_idx_1863_);
v_idx_1835_ = v_idx_1858_;
v___y_1836_ = v___x_1861_;
v_pos_1837_ = v_pos_1862_;
v_idx_1838_ = v_idx_1863_;
goto v___jp_1834_;
}
}
else
{
lean_object* v_err_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_err_1864_ = lean_ctor_get(v___x_1861_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v___x_1861_, 0);
lean_dec(v_unused_1872_);
v___x_1866_ = v___x_1861_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_err_1864_);
lean_dec(v___x_1861_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
lean_inc_ref(v_pos_1857_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v_pos_1857_);
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_pos_1857_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_err_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_inc(v_idx_1858_);
v_idx_1835_ = v_idx_1858_;
v___y_1836_ = v___x_1869_;
v_pos_1837_ = v_pos_1857_;
v_idx_1838_ = v_idx_1858_;
goto v___jp_1834_;
}
}
}
}
}
v___jp_1873_:
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_nat_dec_eq(v_idx_1874_, v_idx_1877_);
lean_dec(v_idx_1874_);
if (v___x_1878_ == 0)
{
lean_dec(v_idx_1877_);
lean_dec_ref(v_pos_1876_);
return v___y_1875_;
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref(v___y_1875_);
v___x_1879_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143);
lean_inc_ref(v_pos_1876_);
v___x_1880_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1879_, v___f_1153_, v_pos_1876_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_dec_ref(v_pos_1876_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_dec(v_idx_1877_);
return v___x_1880_;
}
else
{
lean_object* v_pos_1881_; lean_object* v_idx_1882_; 
v_pos_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_pos_1881_);
v_idx_1882_ = lean_ctor_get(v_pos_1881_, 1);
lean_inc(v_idx_1882_);
v_idx_1855_ = v_idx_1877_;
v___y_1856_ = v___x_1880_;
v_pos_1857_ = v_pos_1881_;
v_idx_1858_ = v_idx_1882_;
goto v___jp_1854_;
}
}
else
{
lean_object* v_err_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_err_1883_ = lean_ctor_get(v___x_1880_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v___x_1880_, 0);
lean_dec(v_unused_1891_);
v___x_1885_ = v___x_1880_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_err_1883_);
lean_dec(v___x_1880_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
lean_inc_ref(v_pos_1876_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_pos_1876_);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_pos_1876_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_err_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_inc(v_idx_1877_);
v_idx_1855_ = v_idx_1877_;
v___y_1856_ = v___x_1888_;
v_pos_1857_ = v_pos_1876_;
v_idx_1858_ = v_idx_1877_;
goto v___jp_1854_;
}
}
}
}
}
v___jp_1893_:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_nat_dec_eq(v_idx_1894_, v_idx_1897_);
lean_dec(v_idx_1894_);
if (v___x_1898_ == 0)
{
lean_dec(v_idx_1897_);
lean_dec_ref(v_pos_1896_);
return v___y_1895_;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec_ref(v___y_1895_);
v___x_1899_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147);
lean_inc_ref(v_pos_1896_);
v___x_1900_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1899_, v___f_1892_, v_pos_1896_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_dec_ref(v_pos_1896_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_dec(v_idx_1897_);
return v___x_1900_;
}
else
{
lean_object* v_pos_1901_; lean_object* v_idx_1902_; 
v_pos_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_pos_1901_);
v_idx_1902_ = lean_ctor_get(v_pos_1901_, 1);
lean_inc(v_idx_1902_);
v_idx_1874_ = v_idx_1897_;
v___y_1875_ = v___x_1900_;
v_pos_1876_ = v_pos_1901_;
v_idx_1877_ = v_idx_1902_;
goto v___jp_1873_;
}
}
else
{
lean_object* v_err_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_err_1903_ = lean_ctor_get(v___x_1900_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v___x_1900_, 0);
lean_dec(v_unused_1911_);
v___x_1905_ = v___x_1900_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_err_1903_);
lean_dec(v___x_1900_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
lean_inc_ref(v_pos_1896_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v_pos_1896_);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_pos_1896_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_err_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_inc(v_idx_1897_);
v_idx_1874_ = v_idx_1897_;
v___y_1875_ = v___x_1908_;
v_pos_1876_ = v_pos_1896_;
v_idx_1877_ = v_idx_1897_;
goto v___jp_1873_;
}
}
}
}
}
v___jp_1912_:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_nat_dec_eq(v_idx_1913_, v_idx_1916_);
lean_dec(v_idx_1913_);
if (v___x_1917_ == 0)
{
lean_dec(v_idx_1916_);
lean_dec_ref(v_pos_1915_);
return v___y_1914_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec_ref(v___y_1914_);
v___x_1918_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150);
lean_inc_ref(v_pos_1915_);
v___x_1919_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1918_, v___f_1152_, v_pos_1915_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_dec_ref(v_pos_1915_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_dec(v_idx_1916_);
return v___x_1919_;
}
else
{
lean_object* v_pos_1920_; lean_object* v_idx_1921_; 
v_pos_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_pos_1920_);
v_idx_1921_ = lean_ctor_get(v_pos_1920_, 1);
lean_inc(v_idx_1921_);
v_idx_1894_ = v_idx_1916_;
v___y_1895_ = v___x_1919_;
v_pos_1896_ = v_pos_1920_;
v_idx_1897_ = v_idx_1921_;
goto v___jp_1893_;
}
}
else
{
lean_object* v_err_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_err_1922_ = lean_ctor_get(v___x_1919_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v___x_1919_, 0);
lean_dec(v_unused_1930_);
v___x_1924_ = v___x_1919_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_err_1922_);
lean_dec(v___x_1919_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
lean_inc_ref(v_pos_1915_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v_pos_1915_);
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_pos_1915_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_err_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_inc(v_idx_1916_);
v_idx_1894_ = v_idx_1916_;
v___y_1895_ = v___x_1927_;
v_pos_1896_ = v_pos_1915_;
v_idx_1897_ = v_idx_1916_;
goto v___jp_1893_;
}
}
}
}
}
v___jp_1932_:
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_nat_dec_eq(v_idx_1933_, v_idx_1936_);
lean_dec(v_idx_1933_);
if (v___x_1937_ == 0)
{
lean_dec(v_idx_1936_);
lean_dec_ref(v_pos_1935_);
return v___y_1934_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec_ref(v___y_1934_);
v___x_1938_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154);
lean_inc_ref(v_pos_1935_);
v___x_1939_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1938_, v___f_1931_, v_pos_1935_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_dec_ref(v_pos_1935_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_dec(v_idx_1936_);
return v___x_1939_;
}
else
{
lean_object* v_pos_1940_; lean_object* v_idx_1941_; 
v_pos_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_pos_1940_);
v_idx_1941_ = lean_ctor_get(v_pos_1940_, 1);
lean_inc(v_idx_1941_);
v_idx_1913_ = v_idx_1936_;
v___y_1914_ = v___x_1939_;
v_pos_1915_ = v_pos_1940_;
v_idx_1916_ = v_idx_1941_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_err_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_err_1942_ = lean_ctor_get(v___x_1939_, 1);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v___x_1939_, 0);
lean_dec(v_unused_1950_);
v___x_1944_ = v___x_1939_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_err_1942_);
lean_dec(v___x_1939_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
lean_inc_ref(v_pos_1935_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v_pos_1935_);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_pos_1935_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_err_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_inc(v_idx_1936_);
v_idx_1913_ = v_idx_1936_;
v___y_1914_ = v___x_1947_;
v_pos_1915_ = v_pos_1935_;
v_idx_1916_ = v_idx_1936_;
goto v___jp_1912_;
}
}
}
}
}
v___jp_1951_:
{
lean_object* v_idx_1954_; lean_object* v_idx_1955_; uint8_t v___x_1956_; 
v_idx_1954_ = lean_ctor_get(v_a_1150_, 1);
lean_inc(v_idx_1954_);
lean_dec_ref(v_a_1150_);
v_idx_1955_ = lean_ctor_get(v_pos_1953_, 1);
lean_inc(v_idx_1955_);
v___x_1956_ = lean_nat_dec_eq(v_idx_1954_, v_idx_1955_);
lean_dec(v_idx_1954_);
if (v___x_1956_ == 0)
{
lean_dec(v_idx_1955_);
lean_dec_ref(v_pos_1953_);
return v___y_1952_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec_ref(v___y_1952_);
v___x_1957_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157);
lean_inc_ref(v_pos_1953_);
v___x_1958_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1957_, v___f_1151_, v_pos_1953_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec_ref(v_pos_1953_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec(v_idx_1955_);
return v___x_1958_;
}
else
{
lean_object* v_pos_1959_; lean_object* v_idx_1960_; 
v_pos_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_pos_1959_);
v_idx_1960_ = lean_ctor_get(v_pos_1959_, 1);
lean_inc(v_idx_1960_);
v_idx_1933_ = v_idx_1955_;
v___y_1934_ = v___x_1958_;
v_pos_1935_ = v_pos_1959_;
v_idx_1936_ = v_idx_1960_;
goto v___jp_1932_;
}
}
else
{
lean_object* v_err_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_err_1961_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_1969_);
v___x_1963_ = v___x_1958_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_err_1961_);
lean_dec(v___x_1958_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
lean_inc_ref(v_pos_1953_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_pos_1953_);
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_pos_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_err_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_inc(v_idx_1955_);
v_idx_1933_ = v_idx_1955_;
v___y_1934_ = v___x_1966_;
v_pos_1935_ = v_pos_1953_;
v_idx_1936_ = v_idx_1955_;
goto v___jp_1932_;
}
}
}
}
}
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1983_){
_start:
{
uint8_t v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = 32;
v___x_1985_ = lean_uint8_dec_eq(v_b_1983_, v___x_1984_);
if (v___x_1985_ == 0)
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
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_1983_ = stack[0].m_num;
uint8_t v_res_1988_;
v_res_1988_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_1983_);
stack->m_num = v_res_1988_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1989_){
_start:
{
uint8_t v_b_boxed_1990_; uint8_t v_res_1991_; lean_object* v_r_1992_; 
v_b_boxed_1990_ = lean_unbox(v_b_1989_);
v_res_1991_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1990_);
v_r_1992_ = lean_box(v_res_1991_);
return v_r_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v_maxUriLength_2004_; lean_object* v___f_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v_snd_2008_; lean_object* v_snd_2009_; uint8_t v___x_2010_; 
v_maxUriLength_2004_ = lean_ctor_get(v_limits_1997_, 4);
v___f_2005_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_2006_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1998_);
v___x_2007_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2005_, v_maxUriLength_2004_, v___x_2006_, v_a_1998_);
v_snd_2008_ = lean_ctor_get(v___x_2007_, 1);
lean_inc(v_snd_2008_);
v_snd_2009_ = lean_ctor_get(v_snd_2008_, 1);
v___x_2010_ = lean_unbox(v_snd_2009_);
if (v___x_2010_ == 0)
{
lean_object* v_fst_2011_; lean_object* v_fst_2012_; lean_object* v_array_2013_; lean_object* v_idx_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2041_; 
v_fst_2011_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_fst_2011_);
lean_dec_ref(v___x_2007_);
v_fst_2012_ = lean_ctor_get(v_snd_2008_, 0);
lean_inc(v_fst_2012_);
lean_dec(v_snd_2008_);
v_array_2013_ = lean_ctor_get(v_a_1998_, 0);
v_idx_2014_ = lean_ctor_get(v_a_1998_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2016_ = v_a_1998_;
v_isShared_2017_ = v_isSharedCheck_2041_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_idx_2014_);
lean_inc(v_array_2013_);
lean_dec(v_a_1998_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2041_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v_lower_2019_; lean_object* v_upper_2020_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___y_2038_; uint8_t v___x_2040_; 
v___x_2035_ = lean_nat_add(v_idx_2014_, v_fst_2011_);
lean_dec(v_fst_2011_);
v___x_2036_ = lean_byte_array_size(v_array_2013_);
v___x_2040_ = lean_nat_dec_le(v_idx_2014_, v___x_2006_);
if (v___x_2040_ == 0)
{
v___y_2038_ = v_idx_2014_;
goto v___jp_2037_;
}
else
{
lean_dec(v_idx_2014_);
v___y_2038_ = v___x_2006_;
goto v___jp_2037_;
}
v___jp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2021_ = l_ByteArray_toByteSlice(v_array_2013_, v_lower_2019_, v_upper_2020_);
v___x_2022_ = l_ByteSlice_size(v___x_2021_);
v___x_2023_ = lean_nat_dec_eq(v___x_2022_, v_maxUriLength_2004_);
lean_dec(v___x_2022_);
if (v___x_2023_ == 0)
{
lean_del_object(v___x_2016_);
v___y_2000_ = v___x_2021_;
v___y_2001_ = v_fst_2012_;
goto v___jp_1999_;
}
else
{
lean_object* v_array_2024_; lean_object* v_idx_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_array_2024_ = lean_ctor_get(v_fst_2012_, 0);
v_idx_2025_ = lean_ctor_get(v_fst_2012_, 1);
v___x_2026_ = lean_byte_array_size(v_array_2024_);
v___x_2027_ = lean_nat_dec_lt(v_idx_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_del_object(v___x_2016_);
v___y_2000_ = v___x_2021_;
v___y_2001_ = v_fst_2012_;
goto v___jp_1999_;
}
else
{
uint8_t v___x_2028_; uint8_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2028_ = lean_byte_array_fget(v_array_2024_, v_idx_2025_);
v___x_2029_ = 32;
v___x_2030_ = lean_uint8_dec_eq(v___x_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2033_; 
lean_dec_ref(v___x_2021_);
v___x_2031_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 1);
lean_ctor_set(v___x_2016_, 1, v___x_2031_);
lean_ctor_set(v___x_2016_, 0, v_fst_2012_);
v___x_2033_ = v___x_2016_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_fst_2012_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
else
{
lean_del_object(v___x_2016_);
v___y_2000_ = v___x_2021_;
v___y_2001_ = v_fst_2012_;
goto v___jp_1999_;
}
}
}
}
v___jp_2037_:
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_nat_dec_le(v___x_2035_, v___x_2036_);
if (v___x_2039_ == 0)
{
lean_dec(v___x_2035_);
v_lower_2019_ = v___y_2038_;
v_upper_2020_ = v___x_2036_;
goto v___jp_2018_;
}
else
{
v_lower_2019_ = v___y_2038_;
v_upper_2020_ = v___x_2035_;
goto v___jp_2018_;
}
}
}
}
else
{
lean_object* v_fst_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v___x_2007_);
lean_dec_ref(v_a_1998_);
v_fst_2042_ = lean_ctor_get(v_snd_2008_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_snd_2008_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_snd_2008_, 1);
lean_dec(v_unused_2051_);
v___x_2044_ = v_snd_2008_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_fst_2042_);
lean_dec(v_snd_2008_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_box(0);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 1, v___x_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_fst_2042_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
v___jp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = l_ByteSlice_toByteArray(v___y_2000_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___y_2001_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2052_, v_a_2053_);
lean_dec_ref(v_limits_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_pos_2061_; lean_object* v_array_2062_; lean_object* v_idx_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_pos_2061_ = lean_ctor_get(v___x_2060_, 0);
v_array_2062_ = lean_ctor_get(v_pos_2061_, 0);
v_idx_2063_ = lean_ctor_get(v_pos_2061_, 1);
v___x_2064_ = lean_byte_array_size(v_array_2062_);
v___x_2065_ = lean_nat_dec_lt(v_idx_2063_, v___x_2064_);
if (v___x_2065_ == 0)
{
return v___x_2060_;
}
else
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2073_; 
lean_inc(v_pos_2061_);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; lean_object* v_unused_2075_; 
v_unused_2074_ = lean_ctor_get(v___x_2060_, 1);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v___x_2060_, 0);
lean_dec(v_unused_2075_);
v___x_2067_ = v___x_2060_;
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2060_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_2068_ == 0)
{
lean_ctor_set_tag(v___x_2067_, 1);
lean_ctor_set(v___x_2067_, 1, v___x_2069_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_pos_2061_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___y_2089_; lean_object* v_pos_2090_; lean_object* v_res_2091_; lean_object* v_pos_2095_; lean_object* v_res_2096_; lean_object* v___x_2135_; 
v___x_2135_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_pos_2136_; lean_object* v_res_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2167_; 
v_pos_2136_ = lean_ctor_get(v___x_2135_, 0);
v_res_2137_ = lean_ctor_get(v___x_2135_, 1);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2139_ = v___x_2135_;
v_isShared_2140_ = v_isSharedCheck_2167_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_res_2137_);
lean_inc(v_pos_2136_);
lean_dec(v___x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2167_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_array_2141_; lean_object* v_idx_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_array_2141_ = lean_ctor_get(v_pos_2136_, 0);
v_idx_2142_ = lean_ctor_get(v_pos_2136_, 1);
v___x_2143_ = lean_byte_array_size(v_array_2141_);
v___x_2144_ = lean_nat_dec_lt(v_idx_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
lean_dec(v_res_2137_);
v___x_2145_ = lean_box(0);
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 1);
lean_ctor_set(v___x_2139_, 1, v___x_2145_);
v___x_2147_ = v___x_2139_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_pos_2136_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
else
{
uint8_t v___x_2149_; uint8_t v_got_2150_; uint8_t v___x_2151_; 
v___x_2149_ = 32;
v_got_2150_ = lean_byte_array_fget(v_array_2141_, v_idx_2142_);
v___x_2151_ = lean_uint8_dec_eq(v_got_2150_, v___x_2149_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
lean_dec(v_res_2137_);
v___x_2152_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 1);
lean_ctor_set(v___x_2139_, 1, v___x_2152_);
v___x_2154_ = v___x_2139_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_pos_2136_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
else
{
lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2164_; 
lean_inc(v_idx_2142_);
lean_inc_ref(v_array_2141_);
lean_del_object(v___x_2139_);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_pos_2136_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; lean_object* v_unused_2166_; 
v_unused_2165_ = lean_ctor_get(v_pos_2136_, 1);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_pos_2136_, 0);
lean_dec(v_unused_2166_);
v___x_2157_ = v_pos_2136_;
v_isShared_2158_ = v_isSharedCheck_2164_;
goto v_resetjp_2156_;
}
else
{
lean_dec(v_pos_2136_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2164_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2159_ = lean_unsigned_to_nat(1u);
v___x_2160_ = lean_nat_add(v_idx_2142_, v___x_2159_);
lean_dec(v_idx_2142_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v___x_2160_);
v___x_2162_ = v___x_2157_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_array_2141_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
v_pos_2095_ = v___x_2162_;
v_res_2096_ = v_res_2137_;
goto v___jp_2094_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_pos_2168_; lean_object* v_res_2169_; 
v_pos_2168_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_pos_2168_);
v_res_2169_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_res_2169_);
lean_dec_ref_known(v___x_2135_, 2);
v_pos_2095_ = v_pos_2168_;
v_res_2096_ = v_res_2169_;
goto v___jp_2094_;
}
else
{
lean_object* v_pos_2170_; lean_object* v_err_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
v_pos_2170_ = lean_ctor_get(v___x_2135_, 0);
v_err_2171_ = lean_ctor_get(v___x_2135_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2135_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_err_2171_);
lean_inc(v_pos_2170_);
lean_dec(v___x_2135_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_pos_2170_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_err_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
v___jp_2088_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___y_2089_);
lean_ctor_set(v___x_2092_, 1, v_res_2091_);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v_pos_2090_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
return v___x_2093_;
}
v___jp_2094_:
{
lean_object* v___f_2097_; lean_object* v___x_2098_; 
v___f_2097_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_2098_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_2097_, v_res_2096_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2107_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 1);
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_pos_2095_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
return v___x_2105_;
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2109_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_pos_2095_);
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
lean_object* v_pos_2114_; 
v_pos_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_pos_2114_);
lean_dec_ref_known(v___x_2113_, 2);
v___y_2089_ = v_a_2108_;
v_pos_2090_ = v_pos_2114_;
v_res_2091_ = v_res_2111_;
goto v___jp_2088_;
}
else
{
lean_object* v_pos_2115_; lean_object* v_err_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_res_2111_);
lean_dec(v_a_2108_);
v_pos_2115_ = lean_ctor_get(v___x_2113_, 0);
v_err_2116_ = lean_ctor_get(v___x_2113_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2113_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_err_2116_);
lean_inc(v_pos_2115_);
lean_dec(v___x_2113_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_pos_2115_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_err_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_pos_2124_; lean_object* v_res_2125_; 
v_pos_2124_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_pos_2124_);
v_res_2125_ = lean_ctor_get(v___x_2109_, 1);
lean_inc(v_res_2125_);
lean_dec_ref_known(v___x_2109_, 2);
v___y_2089_ = v_a_2108_;
v_pos_2090_ = v_pos_2124_;
v_res_2091_ = v_res_2125_;
goto v___jp_2088_;
}
else
{
lean_object* v_pos_2126_; lean_object* v_err_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_a_2108_);
v_pos_2126_ = lean_ctor_get(v___x_2109_, 0);
v_err_2127_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2109_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_err_2127_);
lean_inc(v_pos_2126_);
lean_dec(v___x_2109_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_pos_2126_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_err_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2179_, v_a_2180_);
lean_dec_ref(v_limits_2179_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v___y_2188_; uint8_t v___y_2192_; uint8_t v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v_pos_2204_; uint8_t v_res_2205_; lean_object* v___x_2236_; 
v___x_2236_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2185_, v_a_2186_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_pos_2237_; lean_object* v___x_2238_; 
v_pos_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_pos_2237_);
lean_dec_ref_known(v___x_2236_, 2);
v___x_2238_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2237_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_pos_2239_; lean_object* v_res_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2271_; 
v_pos_2239_ = lean_ctor_get(v___x_2238_, 0);
v_res_2240_ = lean_ctor_get(v___x_2238_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2242_ = v___x_2238_;
v_isShared_2243_ = v_isSharedCheck_2271_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_res_2240_);
lean_inc(v_pos_2239_);
lean_dec(v___x_2238_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2271_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_array_2244_; lean_object* v_idx_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v_array_2244_ = lean_ctor_get(v_pos_2239_, 0);
v_idx_2245_ = lean_ctor_get(v_pos_2239_, 1);
v___x_2246_ = lean_byte_array_size(v_array_2244_);
v___x_2247_ = lean_nat_dec_lt(v_idx_2245_, v___x_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
lean_dec(v_res_2240_);
v___x_2248_ = lean_box(0);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 1);
lean_ctor_set(v___x_2242_, 1, v___x_2248_);
v___x_2250_ = v___x_2242_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_pos_2239_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
uint8_t v___x_2252_; uint8_t v_got_2253_; uint8_t v___x_2254_; 
v___x_2252_ = 32;
v_got_2253_ = lean_byte_array_fget(v_array_2244_, v_idx_2245_);
v___x_2254_ = lean_uint8_dec_eq(v_got_2253_, v___x_2252_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
lean_dec(v_res_2240_);
v___x_2255_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 1);
lean_ctor_set(v___x_2242_, 1, v___x_2255_);
v___x_2257_ = v___x_2242_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_pos_2239_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
else
{
lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2268_; 
lean_inc(v_idx_2245_);
lean_inc_ref(v_array_2244_);
lean_del_object(v___x_2242_);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_pos_2239_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; lean_object* v_unused_2270_; 
v_unused_2269_ = lean_ctor_get(v_pos_2239_, 1);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_pos_2239_, 0);
lean_dec(v_unused_2270_);
v___x_2260_ = v_pos_2239_;
v_isShared_2261_ = v_isSharedCheck_2268_;
goto v_resetjp_2259_;
}
else
{
lean_dec(v_pos_2239_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2268_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_nat_add(v_idx_2245_, v___x_2262_);
lean_dec(v_idx_2245_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 1, v___x_2263_);
v___x_2265_ = v___x_2260_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_array_2244_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_unbox(v_res_2240_);
lean_dec(v_res_2240_);
v_pos_2204_ = v___x_2265_;
v_res_2205_ = v___x_2266_;
goto v___jp_2203_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_pos_2272_; lean_object* v_res_2273_; uint8_t v___x_2274_; 
v_pos_2272_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_pos_2272_);
v_res_2273_ = lean_ctor_get(v___x_2238_, 1);
lean_inc(v_res_2273_);
lean_dec_ref_known(v___x_2238_, 2);
v___x_2274_ = lean_unbox(v_res_2273_);
lean_dec(v_res_2273_);
v_pos_2204_ = v_pos_2272_;
v_res_2205_ = v___x_2274_;
goto v___jp_2203_;
}
else
{
lean_object* v_pos_2275_; lean_object* v_err_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
v_pos_2275_ = lean_ctor_get(v___x_2238_, 0);
v_err_2276_ = lean_ctor_get(v___x_2238_, 1);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2238_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_err_2276_);
lean_inc(v_pos_2275_);
lean_dec(v___x_2238_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_pos_2275_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_err_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v_pos_2284_; lean_object* v_err_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
v_pos_2284_ = lean_ctor_get(v___x_2236_, 0);
v_err_2285_ = lean_ctor_get(v___x_2236_, 1);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2236_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_err_2285_);
lean_inc(v_pos_2284_);
lean_dec(v___x_2236_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_pos_2284_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_err_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
v___jp_2187_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_2190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___y_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
return v___x_2190_;
}
v___jp_2191_:
{
if (v___y_2193_ == 0)
{
lean_dec(v___y_2196_);
lean_dec(v___y_2194_);
v___y_2188_ = v___y_2195_;
goto v___jp_2187_;
}
else
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = lean_nat_dec_eq(v___y_2194_, v___x_2197_);
lean_dec(v___y_2194_);
if (v___x_2198_ == 0)
{
lean_dec(v___y_2196_);
v___y_2188_ = v___y_2195_;
goto v___jp_2187_;
}
else
{
uint8_t v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2199_ = 0;
v___x_2200_ = l_Std_Http_Headers_empty;
v___x_2201_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2201_, 0, v___y_2196_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
lean_ctor_set_uint8(v___x_2201_, sizeof(void*)*2, v___y_2192_);
lean_ctor_set_uint8(v___x_2201_, sizeof(void*)*2 + 1, v___x_2199_);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___y_2195_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
return v___x_2202_;
}
}
}
v___jp_2203_:
{
lean_object* v___x_2206_; 
v___x_2206_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2185_, v_pos_2204_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_res_2207_; lean_object* v_snd_2208_; lean_object* v_pos_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2225_; 
v_res_2207_ = lean_ctor_get(v___x_2206_, 1);
lean_inc(v_res_2207_);
v_snd_2208_ = lean_ctor_get(v_res_2207_, 1);
lean_inc(v_snd_2208_);
v_pos_2209_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v___x_2206_, 1);
lean_dec(v_unused_2226_);
v___x_2211_ = v___x_2206_;
v_isShared_2212_ = v_isSharedCheck_2225_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_pos_2209_);
lean_dec(v___x_2206_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2225_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v_fst_2213_; lean_object* v_fst_2214_; lean_object* v_snd_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v_fst_2213_ = lean_ctor_get(v_res_2207_, 0);
lean_inc(v_fst_2213_);
lean_dec(v_res_2207_);
v_fst_2214_ = lean_ctor_get(v_snd_2208_, 0);
lean_inc(v_fst_2214_);
v_snd_2215_ = lean_ctor_get(v_snd_2208_, 1);
lean_inc(v_snd_2215_);
lean_dec(v_snd_2208_);
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_nat_dec_eq(v_fst_2214_, v___x_2216_);
lean_dec(v_fst_2214_);
if (v___x_2217_ == 0)
{
lean_del_object(v___x_2211_);
v___y_2192_ = v_res_2205_;
v___y_2193_ = v___x_2217_;
v___y_2194_ = v_snd_2215_;
v___y_2195_ = v_pos_2209_;
v___y_2196_ = v_fst_2213_;
goto v___jp_2191_;
}
else
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_nat_dec_eq(v_snd_2215_, v___x_2216_);
if (v___x_2218_ == 0)
{
lean_del_object(v___x_2211_);
v___y_2192_ = v_res_2205_;
v___y_2193_ = v___x_2217_;
v___y_2194_ = v_snd_2215_;
v___y_2195_ = v_pos_2209_;
v___y_2196_ = v_fst_2213_;
goto v___jp_2191_;
}
else
{
uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
lean_dec(v_snd_2215_);
v___x_2219_ = 1;
v___x_2220_ = l_Std_Http_Headers_empty;
v___x_2221_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2221_, 0, v_fst_2213_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*2, v_res_2205_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*2 + 1, v___x_2219_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v___x_2221_);
v___x_2223_ = v___x_2211_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_pos_2209_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
lean_object* v_pos_2227_; lean_object* v_err_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_pos_2227_ = lean_ctor_get(v___x_2206_, 0);
v_err_2228_ = lean_ctor_get(v___x_2206_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2206_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_err_2228_);
lean_inc(v_pos_2227_);
lean_dec(v___x_2206_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_pos_2227_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_err_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_2293_, v_a_2294_);
lean_dec_ref(v_limits_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_pos_2299_; uint8_t v_res_2300_; lean_object* v___x_2342_; 
v___x_2342_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_pos_2343_; lean_object* v___x_2344_; 
v_pos_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_pos_2343_);
lean_dec_ref_known(v___x_2342_, 2);
v___x_2344_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2343_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_pos_2345_; lean_object* v_res_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2377_; 
v_pos_2345_ = lean_ctor_get(v___x_2344_, 0);
v_res_2346_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2348_ = v___x_2344_;
v_isShared_2349_ = v_isSharedCheck_2377_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_res_2346_);
lean_inc(v_pos_2345_);
lean_dec(v___x_2344_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2377_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_array_2350_; lean_object* v_idx_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v_array_2350_ = lean_ctor_get(v_pos_2345_, 0);
v_idx_2351_ = lean_ctor_get(v_pos_2345_, 1);
v___x_2352_ = lean_byte_array_size(v_array_2350_);
v___x_2353_ = lean_nat_dec_lt(v_idx_2351_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec(v_res_2346_);
v___x_2354_ = lean_box(0);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 1);
lean_ctor_set(v___x_2348_, 1, v___x_2354_);
v___x_2356_ = v___x_2348_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_pos_2345_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
else
{
uint8_t v___x_2358_; uint8_t v_got_2359_; uint8_t v___x_2360_; 
v___x_2358_ = 32;
v_got_2359_ = lean_byte_array_fget(v_array_2350_, v_idx_2351_);
v___x_2360_ = lean_uint8_dec_eq(v_got_2359_, v___x_2358_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec(v_res_2346_);
v___x_2361_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 1);
lean_ctor_set(v___x_2348_, 1, v___x_2361_);
v___x_2363_ = v___x_2348_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_pos_2345_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2374_; 
lean_inc(v_idx_2351_);
lean_inc_ref(v_array_2350_);
lean_del_object(v___x_2348_);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_pos_2345_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; lean_object* v_unused_2376_; 
v_unused_2375_ = lean_ctor_get(v_pos_2345_, 1);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_pos_2345_, 0);
lean_dec(v_unused_2376_);
v___x_2366_ = v_pos_2345_;
v_isShared_2367_ = v_isSharedCheck_2374_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v_pos_2345_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2374_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_nat_add(v_idx_2351_, v___x_2368_);
lean_dec(v_idx_2351_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2369_);
v___x_2371_ = v___x_2366_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_array_2350_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
uint8_t v___x_2372_; 
v___x_2372_ = lean_unbox(v_res_2346_);
lean_dec(v_res_2346_);
v_pos_2299_ = v___x_2371_;
v_res_2300_ = v___x_2372_;
goto v___jp_2298_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_pos_2378_; lean_object* v_res_2379_; uint8_t v___x_2380_; 
v_pos_2378_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_pos_2378_);
v_res_2379_ = lean_ctor_get(v___x_2344_, 1);
lean_inc(v_res_2379_);
lean_dec_ref_known(v___x_2344_, 2);
v___x_2380_ = lean_unbox(v_res_2379_);
lean_dec(v_res_2379_);
v_pos_2299_ = v_pos_2378_;
v_res_2300_ = v___x_2380_;
goto v___jp_2298_;
}
else
{
lean_object* v_pos_2381_; lean_object* v_err_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
v_pos_2381_ = lean_ctor_get(v___x_2344_, 0);
v_err_2382_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2344_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_err_2382_);
lean_inc(v_pos_2381_);
lean_dec(v___x_2344_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_pos_2381_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_err_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
else
{
lean_object* v_pos_2390_; lean_object* v_err_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v_pos_2390_ = lean_ctor_get(v___x_2342_, 0);
v_err_2391_ = lean_ctor_get(v___x_2342_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2342_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_err_2391_);
lean_inc(v_pos_2390_);
lean_dec(v___x_2342_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_pos_2390_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_err_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
v___jp_2298_:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2296_, v_pos_2299_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_res_2302_; lean_object* v_snd_2303_; lean_object* v_pos_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2331_; 
v_res_2302_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_res_2302_);
v_snd_2303_ = lean_ctor_get(v_res_2302_, 1);
lean_inc(v_snd_2303_);
v_pos_2304_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2331_ == 0)
{
lean_object* v_unused_2332_; 
v_unused_2332_ = lean_ctor_get(v___x_2301_, 1);
lean_dec(v_unused_2332_);
v___x_2306_ = v___x_2301_;
v_isShared_2307_ = v_isSharedCheck_2331_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_pos_2304_);
lean_dec(v___x_2301_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2331_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_fst_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2329_; 
v_fst_2308_ = lean_ctor_get(v_res_2302_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_res_2302_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v_res_2302_, 1);
lean_dec(v_unused_2330_);
v___x_2310_ = v_res_2302_;
v_isShared_2311_ = v_isSharedCheck_2329_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_fst_2308_);
lean_dec(v_res_2302_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2329_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2328_; 
v_fst_2312_ = lean_ctor_get(v_snd_2303_, 0);
v_snd_2313_ = lean_ctor_get(v_snd_2303_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_snd_2303_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2315_ = v_snd_2303_;
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snd_2313_);
lean_inc(v_fst_2312_);
lean_dec(v_snd_2303_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = l_Std_Http_Version_ofNumber_x3f(v_fst_2312_, v_snd_2313_);
lean_dec(v_snd_2313_);
lean_dec(v_fst_2312_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v___x_2317_);
lean_ctor_set(v___x_2315_, 0, v_fst_2308_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_fst_2308_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2320_ = lean_box(v_res_2300_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v___x_2319_);
lean_ctor_set(v___x_2310_, 0, v___x_2320_);
v___x_2322_ = v___x_2310_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2319_);
v___x_2322_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2322_);
v___x_2324_ = v___x_2306_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_pos_2304_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2333_; lean_object* v_err_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_pos_2333_ = lean_ctor_get(v___x_2301_, 0);
v_err_2334_ = lean_ctor_get(v___x_2301_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2301_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_err_2334_);
lean_inc(v_pos_2333_);
lean_dec(v___x_2301_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_2399_, v_a_2400_);
lean_dec_ref(v_limits_2399_);
return v_res_2401_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_2402_){
_start:
{
uint32_t v___x_2403_; uint32_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2403_ = lean_uint8_to_uint32(v___y_2402_);
v___x_2404_ = 32;
v___x_2405_ = lean_uint32_dec_eq(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
uint32_t v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = 9;
v___x_2407_ = lean_uint32_dec_eq(v___x_2403_, v___x_2406_);
return v___x_2407_;
}
else
{
return v___x_2405_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_2402_ = stack[0].m_num;
uint8_t v_res_2408_;
v_res_2408_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_2402_);
stack->m_num = v_res_2408_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_2409_){
_start:
{
uint8_t v___y_3721__boxed_2410_; uint8_t v_res_2411_; lean_object* v_r_2412_; 
v___y_3721__boxed_2410_ = lean_unbox(v___y_2409_);
v_res_2411_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_3721__boxed_2410_);
v_r_2412_ = lean_box(v_res_2411_);
return v_r_2412_;
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(uint8_t v___y_2413_){
_start:
{
uint32_t v___x_2414_; uint32_t v___x_2420_; uint8_t v___x_2421_; 
v___x_2414_ = lean_uint8_to_uint32(v___y_2413_);
v___x_2420_ = 33;
v___x_2421_ = lean_uint32_dec_le(v___x_2420_, v___x_2414_);
if (v___x_2421_ == 0)
{
goto v___jp_2415_;
}
else
{
uint32_t v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = 126;
v___x_2423_ = lean_uint32_dec_le(v___x_2414_, v___x_2422_);
if (v___x_2423_ == 0)
{
goto v___jp_2415_;
}
else
{
return v___x_2423_;
}
}
v___jp_2415_:
{
uint32_t v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = 32;
v___x_2417_ = lean_uint32_dec_eq(v___x_2414_, v___x_2416_);
if (v___x_2417_ == 0)
{
uint32_t v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = 9;
v___x_2419_ = lean_uint32_dec_eq(v___x_2414_, v___x_2418_);
return v___x_2419_;
}
else
{
return v___x_2417_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_2413_ = stack[0].m_num;
uint8_t v_res_2424_;
v_res_2424_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(v___y_2413_);
stack->m_num = v_res_2424_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed(lean_object* v___y_2425_){
_start:
{
uint8_t v___y_3741__boxed_2426_; uint8_t v_res_2427_; lean_object* v_r_2428_; 
v___y_3741__boxed_2426_ = lean_unbox(v___y_2425_);
v_res_2427_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(v___y_3741__boxed_2426_);
v_r_2428_ = lean_box(v_res_2427_);
return v_r_2428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_2429_, lean_object* v_pos_2430_){
_start:
{
lean_object* v_str_2431_; lean_object* v_startInclusive_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; uint8_t v_decide_2436_; 
v_str_2431_ = lean_ctor_get(v_s_2429_, 0);
v_startInclusive_2432_ = lean_ctor_get(v_s_2429_, 1);
v___x_2433_ = lean_nat_add(v_startInclusive_2432_, v_pos_2430_);
v___x_2434_ = lean_nat_sub(v___x_2433_, v_startInclusive_2432_);
v___x_2435_ = lean_unsigned_to_nat(0u);
v_decide_2436_ = lean_nat_dec_eq(v___x_2434_, v___x_2435_);
if (v_decide_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2445_; uint32_t v___x_2446_; uint32_t v___x_2447_; uint8_t v___x_2448_; 
lean_inc(v_startInclusive_2432_);
lean_inc_ref(v_str_2431_);
v___x_2437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2437_, 0, v_str_2431_);
lean_ctor_set(v___x_2437_, 1, v_startInclusive_2432_);
lean_ctor_set(v___x_2437_, 2, v___x_2433_);
v___x_2438_ = lean_unsigned_to_nat(1u);
v___x_2439_ = lean_nat_sub(v___x_2434_, v___x_2438_);
lean_dec(v___x_2434_);
v___x_2440_ = l_String_Slice_posLE(v___x_2437_, v___x_2439_);
lean_dec_ref_known(v___x_2437_, 3);
v___x_2445_ = lean_nat_add(v_startInclusive_2432_, v___x_2440_);
v___x_2446_ = lean_string_utf8_get_fast(v_str_2431_, v___x_2445_);
lean_dec(v___x_2445_);
v___x_2447_ = 32;
v___x_2448_ = lean_uint32_dec_eq(v___x_2446_, v___x_2447_);
if (v___x_2448_ == 0)
{
uint32_t v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = 9;
v___x_2450_ = lean_uint32_dec_eq(v___x_2446_, v___x_2449_);
if (v___x_2450_ == 0)
{
uint32_t v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = 13;
v___x_2452_ = lean_uint32_dec_eq(v___x_2446_, v___x_2451_);
if (v___x_2452_ == 0)
{
uint32_t v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = 10;
v___x_2454_ = lean_uint32_dec_eq(v___x_2446_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_dec(v___x_2440_);
return v_pos_2430_;
}
else
{
goto v___jp_2441_;
}
}
else
{
goto v___jp_2441_;
}
}
else
{
goto v___jp_2441_;
}
}
else
{
goto v___jp_2441_;
}
v___jp_2441_:
{
lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2442_ = lean_nat_add(v___x_2440_, v___x_2438_);
v___x_2443_ = lean_nat_dec_le(v___x_2442_, v_pos_2430_);
lean_dec(v___x_2442_);
if (v___x_2443_ == 0)
{
lean_dec(v___x_2440_);
return v_pos_2430_;
}
else
{
lean_dec(v_pos_2430_);
v_pos_2430_ = v___x_2440_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2434_);
lean_dec(v___x_2433_);
return v_pos_2430_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_2455_, lean_object* v_pos_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_2455_, v_pos_2456_);
lean_dec_ref(v_s_2455_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_pos_2466_; lean_object* v_pos_2470_; lean_object* v_maxHeaderNameLength_2473_; lean_object* v_maxHeaderValueLength_2474_; lean_object* v_maxSpaceSequence_2475_; lean_object* v___f_2476_; lean_object* v___x_2477_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2537_; lean_object* v_pos_2538_; lean_object* v_res_2539_; lean_object* v___x_2545_; lean_object* v_snd_2546_; lean_object* v_snd_2547_; uint8_t v___x_2548_; 
v_maxHeaderNameLength_2473_ = lean_ctor_get(v_limits_2463_, 6);
v_maxHeaderValueLength_2474_ = lean_ctor_get(v_limits_2463_, 7);
v_maxSpaceSequence_2475_ = lean_ctor_get(v_limits_2463_, 8);
v___f_2476_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2477_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2464_);
v___x_2545_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2476_, v_maxHeaderNameLength_2473_, v___x_2477_, v_a_2464_);
v_snd_2546_ = lean_ctor_get(v___x_2545_, 1);
lean_inc(v_snd_2546_);
v_snd_2547_ = lean_ctor_get(v_snd_2546_, 1);
v___x_2548_ = lean_unbox(v_snd_2547_);
if (v___x_2548_ == 0)
{
lean_object* v_fst_2549_; lean_object* v_fst_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2708_; 
v_fst_2549_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_fst_2549_);
lean_dec_ref(v___x_2545_);
v_fst_2550_ = lean_ctor_get(v_snd_2546_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_snd_2546_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v_snd_2546_, 1);
lean_dec(v_unused_2709_);
v___x_2552_ = v_snd_2546_;
v_isShared_2553_ = v_isSharedCheck_2708_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_fst_2550_);
lean_dec(v_snd_2546_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2708_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
uint8_t v___x_2554_; 
v___x_2554_ = lean_nat_dec_eq(v_fst_2549_, v___x_2477_);
if (v___x_2554_ == 0)
{
lean_object* v_array_2555_; lean_object* v_idx_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2703_; 
v_array_2555_ = lean_ctor_get(v_a_2464_, 0);
v_idx_2556_ = lean_ctor_get(v_a_2464_, 1);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_a_2464_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2558_ = v_a_2464_;
v_isShared_2559_ = v_isSharedCheck_2703_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_idx_2556_);
lean_inc(v_array_2555_);
lean_dec(v_a_2464_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2703_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___f_2560_; lean_object* v___y_2562_; lean_object* v_pos_2563_; lean_object* v_res_2564_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v_lower_2594_; lean_object* v_upper_2595_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___f_2606_; lean_object* v___y_2608_; lean_object* v_pos_2609_; lean_object* v___y_2636_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___y_2694_; uint8_t v___x_2702_; 
v___f_2560_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___f_2606_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_2691_ = lean_nat_add(v_idx_2556_, v_fst_2549_);
lean_dec(v_fst_2549_);
v___x_2692_ = lean_byte_array_size(v_array_2555_);
v___x_2702_ = lean_nat_dec_le(v_idx_2556_, v___x_2477_);
if (v___x_2702_ == 0)
{
v___y_2694_ = v_idx_2556_;
goto v___jp_2693_;
}
else
{
lean_dec(v_idx_2556_);
v___y_2694_ = v___x_2477_;
goto v___jp_2693_;
}
v___jp_2561_:
{
lean_object* v___x_2565_; lean_object* v_snd_2566_; lean_object* v_snd_2567_; uint8_t v___x_2568_; 
v___x_2565_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2560_, v_maxSpaceSequence_2475_, v___x_2477_, v_pos_2563_);
v_snd_2566_ = lean_ctor_get(v___x_2565_, 1);
lean_inc(v_snd_2566_);
lean_dec_ref(v___x_2565_);
v_snd_2567_ = lean_ctor_get(v_snd_2566_, 1);
v___x_2568_ = lean_unbox(v_snd_2567_);
if (v___x_2568_ == 0)
{
lean_object* v_fst_2569_; lean_object* v_array_2570_; lean_object* v_idx_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_fst_2569_ = lean_ctor_get(v_snd_2566_, 0);
lean_inc(v_fst_2569_);
lean_dec(v_snd_2566_);
v_array_2570_ = lean_ctor_get(v_fst_2569_, 0);
v_idx_2571_ = lean_ctor_get(v_fst_2569_, 1);
v___x_2572_ = lean_byte_array_size(v_array_2570_);
v___x_2573_ = lean_nat_dec_lt(v_idx_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
v___y_2537_ = v___y_2562_;
v_pos_2538_ = v_fst_2569_;
v_res_2539_ = v_res_2564_;
goto v___jp_2536_;
}
else
{
uint8_t v___x_2574_; uint32_t v___x_2575_; uint32_t v___x_2576_; uint8_t v___x_2577_; 
v___x_2574_ = lean_byte_array_fget(v_array_2570_, v_idx_2571_);
v___x_2575_ = lean_uint8_to_uint32(v___x_2574_);
v___x_2576_ = 32;
v___x_2577_ = lean_uint32_dec_eq(v___x_2575_, v___x_2576_);
if (v___x_2577_ == 0)
{
uint32_t v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = 9;
v___x_2579_ = lean_uint32_dec_eq(v___x_2575_, v___x_2578_);
if (v___x_2579_ == 0)
{
v___y_2537_ = v___y_2562_;
v_pos_2538_ = v_fst_2569_;
v_res_2539_ = v_res_2564_;
goto v___jp_2536_;
}
else
{
lean_dec(v_res_2564_);
lean_dec_ref(v___y_2562_);
v_pos_2470_ = v_fst_2569_;
goto v___jp_2469_;
}
}
else
{
lean_dec(v_res_2564_);
lean_dec_ref(v___y_2562_);
v_pos_2470_ = v_fst_2569_;
goto v___jp_2469_;
}
}
}
else
{
lean_object* v_fst_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_res_2564_);
lean_dec_ref(v___y_2562_);
v_fst_2580_ = lean_ctor_get(v_snd_2566_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_snd_2566_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v_snd_2566_, 1);
lean_dec(v_unused_2589_);
v___x_2582_ = v_snd_2566_;
v_isShared_2583_ = v_isSharedCheck_2588_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_fst_2580_);
lean_dec(v_snd_2566_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2588_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_box(0);
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 1);
lean_ctor_set(v___x_2582_, 1, v___x_2584_);
v___x_2586_ = v___x_2582_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_fst_2580_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___x_2584_);
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
v___jp_2590_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = l_ByteArray_toByteSlice(v___y_2592_, v_lower_2594_, v_upper_2595_);
v___x_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
v___y_2562_ = v___y_2591_;
v_pos_2563_ = v___y_2593_;
v_res_2564_ = v___x_2597_;
goto v___jp_2561_;
}
v___jp_2598_:
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_nat_dec_le(v___y_2603_, v___y_2599_);
if (v___x_2605_ == 0)
{
lean_dec(v___y_2603_);
v___y_2591_ = v___y_2600_;
v___y_2592_ = v___y_2601_;
v___y_2593_ = v___y_2602_;
v_lower_2594_ = v___y_2604_;
v_upper_2595_ = v___y_2599_;
goto v___jp_2590_;
}
else
{
lean_dec(v___y_2599_);
v___y_2591_ = v___y_2600_;
v___y_2592_ = v___y_2601_;
v___y_2593_ = v___y_2602_;
v_lower_2594_ = v___y_2604_;
v_upper_2595_ = v___y_2603_;
goto v___jp_2590_;
}
}
v___jp_2607_:
{
lean_object* v___x_2610_; lean_object* v_snd_2611_; lean_object* v_snd_2612_; uint8_t v___x_2613_; 
lean_inc_ref(v_pos_2609_);
v___x_2610_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2606_, v_maxHeaderValueLength_2474_, v___x_2477_, v_pos_2609_);
v_snd_2611_ = lean_ctor_get(v___x_2610_, 1);
lean_inc(v_snd_2611_);
v_snd_2612_ = lean_ctor_get(v_snd_2611_, 1);
v___x_2613_ = lean_unbox(v_snd_2612_);
if (v___x_2613_ == 0)
{
lean_object* v_fst_2614_; lean_object* v_fst_2615_; lean_object* v_array_2616_; lean_object* v_idx_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v_fst_2614_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_fst_2614_);
lean_dec_ref(v___x_2610_);
v_fst_2615_ = lean_ctor_get(v_snd_2611_, 0);
lean_inc(v_fst_2615_);
lean_dec(v_snd_2611_);
v_array_2616_ = lean_ctor_get(v_pos_2609_, 0);
lean_inc_ref(v_array_2616_);
v_idx_2617_ = lean_ctor_get(v_pos_2609_, 1);
lean_inc(v_idx_2617_);
lean_dec_ref(v_pos_2609_);
v___x_2618_ = lean_nat_add(v_idx_2617_, v_fst_2614_);
lean_dec(v_fst_2614_);
v___x_2619_ = lean_byte_array_size(v_array_2616_);
v___x_2620_ = lean_nat_dec_le(v_idx_2617_, v___x_2477_);
if (v___x_2620_ == 0)
{
v___y_2599_ = v___x_2619_;
v___y_2600_ = v___y_2608_;
v___y_2601_ = v_array_2616_;
v___y_2602_ = v_fst_2615_;
v___y_2603_ = v___x_2618_;
v___y_2604_ = v_idx_2617_;
goto v___jp_2598_;
}
else
{
lean_dec(v_idx_2617_);
v___y_2599_ = v___x_2619_;
v___y_2600_ = v___y_2608_;
v___y_2601_ = v_array_2616_;
v___y_2602_ = v_fst_2615_;
v___y_2603_ = v___x_2618_;
v___y_2604_ = v___x_2477_;
goto v___jp_2598_;
}
}
else
{
lean_object* v_fst_2621_; lean_object* v_idx_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2633_; 
lean_dec_ref(v___x_2610_);
v_fst_2621_ = lean_ctor_get(v_snd_2611_, 0);
lean_inc(v_fst_2621_);
lean_dec(v_snd_2611_);
v_idx_2622_ = lean_ctor_get(v_pos_2609_, 1);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_pos_2609_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; 
v_unused_2634_ = lean_ctor_get(v_pos_2609_, 0);
lean_dec(v_unused_2634_);
v___x_2624_ = v_pos_2609_;
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_idx_2622_);
lean_dec(v_pos_2609_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_idx_2626_; uint8_t v___x_2627_; 
v_idx_2626_ = lean_ctor_get(v_fst_2621_, 1);
v___x_2627_ = lean_nat_dec_eq(v_idx_2622_, v_idx_2626_);
lean_dec(v_idx_2622_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
lean_dec_ref(v___y_2608_);
v___x_2628_ = lean_box(0);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 1, v___x_2628_);
lean_ctor_set(v___x_2624_, 0, v_fst_2621_);
v___x_2630_ = v___x_2624_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_fst_2621_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
else
{
lean_object* v___x_2632_; 
lean_del_object(v___x_2624_);
v___x_2632_ = lean_box(0);
v___y_2562_ = v___y_2608_;
v_pos_2563_ = v_fst_2621_;
v_res_2564_ = v___x_2632_;
goto v___jp_2561_;
}
}
}
}
v___jp_2635_:
{
lean_object* v_array_2637_; lean_object* v_idx_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v_array_2637_ = lean_ctor_get(v_fst_2550_, 0);
v_idx_2638_ = lean_ctor_get(v_fst_2550_, 1);
v___x_2639_ = lean_byte_array_size(v_array_2637_);
v___x_2640_ = lean_nat_dec_lt(v_idx_2638_, v___x_2639_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_dec_ref(v___y_2636_);
lean_dec_ref(v_array_2555_);
v___x_2641_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 1);
lean_ctor_set(v___x_2558_, 1, v___x_2641_);
lean_ctor_set(v___x_2558_, 0, v_fst_2550_);
v___x_2643_ = v___x_2558_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_fst_2550_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
else
{
uint8_t v___x_2645_; uint8_t v_got_2646_; uint8_t v___x_2647_; 
v___x_2645_ = 58;
v_got_2646_ = lean_byte_array_fget(v_array_2637_, v_idx_2638_);
v___x_2647_ = lean_uint8_dec_eq(v_got_2646_, v___x_2645_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
lean_dec_ref(v___y_2636_);
lean_dec_ref(v_array_2555_);
v___x_2648_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 1);
lean_ctor_set(v___x_2558_, 1, v___x_2648_);
lean_ctor_set(v___x_2558_, 0, v_fst_2550_);
v___x_2650_ = v___x_2558_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_fst_2550_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
else
{
lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2688_; 
lean_inc(v_idx_2638_);
lean_inc_ref(v_array_2637_);
lean_del_object(v___x_2558_);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_fst_2550_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; lean_object* v_unused_2690_; 
v_unused_2689_ = lean_ctor_get(v_fst_2550_, 1);
lean_dec(v_unused_2689_);
v_unused_2690_ = lean_ctor_get(v_fst_2550_, 0);
lean_dec(v_unused_2690_);
v___x_2653_ = v_fst_2550_;
v_isShared_2654_ = v_isSharedCheck_2688_;
goto v_resetjp_2652_;
}
else
{
lean_dec(v_fst_2550_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2688_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2655_ = lean_unsigned_to_nat(1u);
v___x_2656_ = lean_nat_add(v_idx_2638_, v___x_2655_);
lean_dec(v_idx_2638_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2656_);
v___x_2658_ = v___x_2653_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_array_2637_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2659_; lean_object* v_snd_2660_; lean_object* v_snd_2661_; uint8_t v___x_2662_; 
v___x_2659_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2560_, v_maxSpaceSequence_2475_, v___x_2477_, v___x_2658_);
v_snd_2660_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_snd_2660_);
lean_dec_ref(v___x_2659_);
v_snd_2661_ = lean_ctor_get(v_snd_2660_, 1);
v___x_2662_ = lean_unbox(v_snd_2661_);
if (v___x_2662_ == 0)
{
lean_object* v_fst_2663_; lean_object* v_array_2664_; lean_object* v_idx_2665_; lean_object* v_lower_2666_; lean_object* v_upper_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_fst_2663_ = lean_ctor_get(v_snd_2660_, 0);
lean_inc(v_fst_2663_);
lean_dec(v_snd_2660_);
v_array_2664_ = lean_ctor_get(v_fst_2663_, 0);
v_idx_2665_ = lean_ctor_get(v_fst_2663_, 1);
v_lower_2666_ = lean_ctor_get(v___y_2636_, 0);
lean_inc(v_lower_2666_);
v_upper_2667_ = lean_ctor_get(v___y_2636_, 1);
lean_inc(v_upper_2667_);
lean_dec_ref(v___y_2636_);
v___x_2668_ = l_ByteArray_toByteSlice(v_array_2555_, v_lower_2666_, v_upper_2667_);
v___x_2669_ = lean_byte_array_size(v_array_2664_);
v___x_2670_ = lean_nat_dec_lt(v_idx_2665_, v___x_2669_);
if (v___x_2670_ == 0)
{
v___y_2608_ = v___x_2668_;
v_pos_2609_ = v_fst_2663_;
goto v___jp_2607_;
}
else
{
uint8_t v___x_2671_; uint32_t v___x_2672_; uint32_t v___x_2673_; uint8_t v___x_2674_; 
v___x_2671_ = lean_byte_array_fget(v_array_2664_, v_idx_2665_);
v___x_2672_ = lean_uint8_to_uint32(v___x_2671_);
v___x_2673_ = 32;
v___x_2674_ = lean_uint32_dec_eq(v___x_2672_, v___x_2673_);
if (v___x_2674_ == 0)
{
uint32_t v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = 9;
v___x_2676_ = lean_uint32_dec_eq(v___x_2672_, v___x_2675_);
if (v___x_2676_ == 0)
{
v___y_2608_ = v___x_2668_;
v_pos_2609_ = v_fst_2663_;
goto v___jp_2607_;
}
else
{
lean_dec_ref(v___x_2668_);
v_pos_2466_ = v_fst_2663_;
goto v___jp_2465_;
}
}
else
{
lean_dec_ref(v___x_2668_);
v_pos_2466_ = v_fst_2663_;
goto v___jp_2465_;
}
}
}
else
{
lean_object* v_fst_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2685_; 
lean_dec_ref(v___y_2636_);
lean_dec_ref(v_array_2555_);
v_fst_2677_ = lean_ctor_get(v_snd_2660_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_snd_2660_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v_snd_2660_, 1);
lean_dec(v_unused_2686_);
v___x_2679_ = v_snd_2660_;
v_isShared_2680_ = v_isSharedCheck_2685_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_fst_2677_);
lean_dec(v_snd_2660_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2685_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2681_ = lean_box(0);
if (v_isShared_2680_ == 0)
{
lean_ctor_set_tag(v___x_2679_, 1);
lean_ctor_set(v___x_2679_, 1, v___x_2681_);
v___x_2683_ = v___x_2679_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_fst_2677_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
}
}
}
v___jp_2693_:
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_nat_dec_le(v___x_2691_, v___x_2692_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2697_; 
lean_dec(v___x_2691_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___x_2692_);
lean_ctor_set(v___x_2552_, 0, v___y_2694_);
v___x_2697_ = v___x_2552_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___y_2694_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
v___y_2636_ = v___x_2697_;
goto v___jp_2635_;
}
}
else
{
lean_object* v___x_2700_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___x_2691_);
lean_ctor_set(v___x_2552_, 0, v___y_2694_);
v___x_2700_ = v___x_2552_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___y_2694_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2691_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
v___y_2636_ = v___x_2700_;
goto v___jp_2635_;
}
}
}
}
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2706_; 
lean_dec(v_fst_2550_);
lean_dec(v_fst_2549_);
v___x_2704_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2553_ == 0)
{
lean_ctor_set_tag(v___x_2552_, 1);
lean_ctor_set(v___x_2552_, 1, v___x_2704_);
lean_ctor_set(v___x_2552_, 0, v_a_2464_);
v___x_2706_ = v___x_2552_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2464_);
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
lean_dec_ref(v___x_2545_);
lean_dec_ref(v_a_2464_);
v_fst_2710_ = lean_ctor_get(v_snd_2546_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_snd_2546_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v_snd_2546_, 1);
lean_dec(v_unused_2719_);
v___x_2712_ = v_snd_2546_;
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_fst_2710_);
lean_dec(v_snd_2546_);
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
v___jp_2478_:
{
lean_object* v___x_2482_; 
v___x_2482_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2481_, v___y_2479_);
lean_dec(v___y_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_pos_2483_; lean_object* v_res_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2497_; 
v_pos_2483_ = lean_ctor_get(v___x_2482_, 0);
v_res_2484_ = lean_ctor_get(v___x_2482_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2486_ = v___x_2482_;
v_isShared_2487_ = v_isSharedCheck_2497_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_res_2484_);
lean_inc(v_pos_2483_);
lean_dec(v___x_2482_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2497_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2488_ = lean_string_utf8_byte_size(v_res_2484_);
lean_inc(v_res_2484_);
v___x_2489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2489_, 0, v_res_2484_);
lean_ctor_set(v___x_2489_, 1, v___x_2477_);
lean_ctor_set(v___x_2489_, 2, v___x_2488_);
v___x_2490_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_2489_, v___x_2488_);
lean_dec_ref_known(v___x_2489_, 3);
v___x_2491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2491_, 0, v_res_2484_);
lean_ctor_set(v___x_2491_, 1, v___x_2477_);
lean_ctor_set(v___x_2491_, 2, v___x_2490_);
v___x_2492_ = l_String_Slice_toString(v___x_2491_);
lean_dec_ref_known(v___x_2491_, 3);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___y_2480_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 1, v___x_2493_);
v___x_2495_ = v___x_2486_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_pos_2483_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
lean_object* v_pos_2498_; lean_object* v_err_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec_ref(v___y_2480_);
v_pos_2498_ = lean_ctor_get(v___x_2482_, 0);
v_err_2499_ = lean_ctor_get(v___x_2482_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2482_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_err_2499_);
lean_inc(v_pos_2498_);
lean_dec(v___x_2482_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_pos_2498_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_err_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
v___jp_2507_:
{
uint8_t v___x_2511_; 
v___x_2511_ = lean_string_validate_utf8(v___y_2510_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
lean_dec_ref(v___y_2510_);
v___x_2512_ = lean_box(0);
v___y_2479_ = v___y_2508_;
v___y_2480_ = v___y_2509_;
v___y_2481_ = v___x_2512_;
goto v___jp_2478_;
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_string_from_utf8_unchecked(v___y_2510_);
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
v___y_2479_ = v___y_2508_;
v___y_2480_ = v___y_2509_;
v___y_2481_ = v___x_2514_;
goto v___jp_2478_;
}
}
v___jp_2515_:
{
lean_object* v___x_2519_; 
v___x_2519_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2518_, v___y_2517_);
lean_dec(v___y_2518_);
if (lean_obj_tag(v___x_2519_) == 0)
{
if (lean_obj_tag(v___y_2516_) == 0)
{
lean_object* v_pos_2520_; lean_object* v_res_2521_; lean_object* v___x_2522_; 
v_pos_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_pos_2520_);
v_res_2521_ = lean_ctor_get(v___x_2519_, 1);
lean_inc(v_res_2521_);
lean_dec_ref_known(v___x_2519_, 2);
v___x_2522_ = l_ByteArray_empty;
v___y_2508_ = v_pos_2520_;
v___y_2509_ = v_res_2521_;
v___y_2510_ = v___x_2522_;
goto v___jp_2507_;
}
else
{
lean_object* v_pos_2523_; lean_object* v_res_2524_; lean_object* v_val_2525_; lean_object* v___x_2526_; 
v_pos_2523_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_pos_2523_);
v_res_2524_ = lean_ctor_get(v___x_2519_, 1);
lean_inc(v_res_2524_);
lean_dec_ref_known(v___x_2519_, 2);
v_val_2525_ = lean_ctor_get(v___y_2516_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v___y_2516_, 1);
v___x_2526_ = l_ByteSlice_toByteArray(v_val_2525_);
v___y_2508_ = v_pos_2523_;
v___y_2509_ = v_res_2524_;
v___y_2510_ = v___x_2526_;
goto v___jp_2507_;
}
}
else
{
lean_object* v_pos_2527_; lean_object* v_err_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v___y_2516_);
v_pos_2527_ = lean_ctor_get(v___x_2519_, 0);
v_err_2528_ = lean_ctor_get(v___x_2519_, 1);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2519_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_err_2528_);
lean_inc(v_pos_2527_);
lean_dec(v___x_2519_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_pos_2527_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_err_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
v___jp_2536_:
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = l_ByteSlice_toByteArray(v___y_2537_);
v___x_2541_ = lean_string_validate_utf8(v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
lean_dec_ref(v___x_2540_);
v___x_2542_ = lean_box(0);
v___y_2516_ = v_res_2539_;
v___y_2517_ = v_pos_2538_;
v___y_2518_ = v___x_2542_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_string_from_utf8_unchecked(v___x_2540_);
v___x_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
v___y_2516_ = v_res_2539_;
v___y_2517_ = v_pos_2538_;
v___y_2518_ = v___x_2544_;
goto v___jp_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2720_, v_a_2721_);
lean_dec_ref(v_limits_2720_);
return v_res_2722_;
}
}
uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2723_, lean_object* v_x_2724_){
_start:
{
if (lean_obj_tag(v_x_2723_) == 0)
{
if (lean_obj_tag(v_x_2724_) == 0)
{
uint8_t v___x_2725_; 
v___x_2725_ = 1;
return v___x_2725_;
}
else
{
uint8_t v___x_2726_; 
v___x_2726_ = 0;
return v___x_2726_;
}
}
else
{
if (lean_obj_tag(v_x_2724_) == 0)
{
uint8_t v___x_2727_; 
v___x_2727_ = 0;
return v___x_2727_;
}
else
{
lean_object* v_val_2728_; lean_object* v_val_2729_; uint8_t v___x_2730_; uint8_t v___x_2731_; uint8_t v___x_2732_; 
v_val_2728_ = lean_ctor_get(v_x_2723_, 0);
v_val_2729_ = lean_ctor_get(v_x_2724_, 0);
v___x_2730_ = lean_unbox(v_val_2728_);
v___x_2731_ = lean_unbox(v_val_2729_);
v___x_2732_ = lean_uint8_dec_eq(v___x_2730_, v___x_2731_);
return v___x_2732_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2723_ = stack[0].m_obj;
lean_object* v_x_2724_ = stack[1].m_obj;
uint8_t v_res_2733_;
v_res_2733_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2723_, v_x_2724_);
stack->m_num = v_res_2733_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2734_, lean_object* v_x_2735_){
_start:
{
uint8_t v_res_2736_; lean_object* v_r_2737_; 
v_res_2736_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2734_, v_x_2735_);
lean_dec(v_x_2735_);
lean_dec(v_x_2734_);
v_r_2737_ = lean_box(v_res_2736_);
return v_r_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_pos_2747_; lean_object* v_res_2748_; lean_object* v___y_2752_; uint8_t v___y_2753_; lean_object* v_pos_2802_; lean_object* v_res_2803_; lean_object* v_array_2808_; lean_object* v_idx_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_array_2808_ = lean_ctor_get(v_a_2745_, 0);
v_idx_2809_ = lean_ctor_get(v_a_2745_, 1);
v___x_2810_ = lean_byte_array_size(v_array_2808_);
v___x_2811_ = lean_nat_dec_lt(v_idx_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_box(0);
v_pos_2802_ = v_a_2745_;
v_res_2803_ = v___x_2812_;
goto v___jp_2801_;
}
else
{
uint8_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2813_ = lean_byte_array_fget(v_array_2808_, v_idx_2809_);
v___x_2814_ = lean_box(v___x_2813_);
v___x_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
v_pos_2802_ = v_a_2745_;
v_res_2803_ = v___x_2815_;
goto v___jp_2801_;
}
v___jp_2746_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_res_2748_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_pos_2747_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
return v___x_2750_;
}
v___jp_2751_:
{
if (v___y_2753_ == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2744_, v___y_2752_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_pos_2755_; lean_object* v_res_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_pos_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_pos_2755_);
v_res_2756_ = lean_ctor_get(v___x_2754_, 1);
lean_inc(v_res_2756_);
lean_dec_ref_known(v___x_2754_, 2);
v___x_2757_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2758_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2757_, v_pos_2755_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_pos_2759_; 
v_pos_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_pos_2759_);
lean_dec_ref_known(v___x_2758_, 2);
v_pos_2747_ = v_pos_2759_;
v_res_2748_ = v_res_2756_;
goto v___jp_2746_;
}
else
{
lean_object* v_pos_2760_; lean_object* v_err_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_res_2756_);
v_pos_2760_ = lean_ctor_get(v___x_2758_, 0);
v_err_2761_ = lean_ctor_get(v___x_2758_, 1);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2758_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_err_2761_);
lean_inc(v_pos_2760_);
lean_dec(v___x_2758_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_pos_2760_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_err_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_pos_2769_; lean_object* v_res_2770_; 
v_pos_2769_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_pos_2769_);
v_res_2770_ = lean_ctor_get(v___x_2754_, 1);
lean_inc(v_res_2770_);
lean_dec_ref_known(v___x_2754_, 2);
v_pos_2747_ = v_pos_2769_;
v_res_2748_ = v_res_2770_;
goto v___jp_2746_;
}
else
{
lean_object* v_pos_2771_; lean_object* v_err_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
v_pos_2771_ = lean_ctor_get(v___x_2754_, 0);
v_err_2772_ = lean_ctor_get(v___x_2754_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2754_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_err_2772_);
lean_inc(v_pos_2771_);
lean_dec(v___x_2754_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_pos_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_err_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2781_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2780_, v___y_2752_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_pos_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2790_; 
v_pos_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v___x_2781_, 1);
lean_dec(v_unused_2791_);
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_pos_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2786_ = lean_box(0);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 1, v___x_2786_);
v___x_2788_ = v___x_2784_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_pos_2782_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_object* v_pos_2792_; lean_object* v_err_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_pos_2792_ = lean_ctor_get(v___x_2781_, 0);
v_err_2793_ = lean_ctor_get(v___x_2781_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2781_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_err_2793_);
lean_inc(v_pos_2792_);
lean_dec(v___x_2781_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_pos_2792_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_err_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
v___jp_2801_:
{
lean_object* v___x_2804_; uint8_t v___x_2805_; 
v___x_2804_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_2805_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2803_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2806_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_2807_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2803_, v___x_2806_);
lean_dec(v_res_2803_);
v___y_2752_ = v_pos_2802_;
v___y_2753_ = v___x_2807_;
goto v___jp_2751_;
}
else
{
lean_dec(v_res_2803_);
v___y_2752_ = v_pos_2802_;
v___y_2753_ = v___x_2805_;
goto v___jp_2751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2816_, v_a_2817_);
lean_dec_ref(v_limits_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2823_){
_start:
{
lean_object* v_array_2824_; lean_object* v_idx_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_array_2824_ = lean_ctor_get(v_a_2823_, 0);
v_idx_2825_ = lean_ctor_get(v_a_2823_, 1);
v___x_2826_ = lean_byte_array_size(v_array_2824_);
v___x_2827_ = lean_nat_dec_lt(v_idx_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2829_, 0, v_a_2823_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
return v___x_2829_;
}
else
{
uint8_t v___x_2830_; uint8_t v_got_2831_; uint8_t v___x_2832_; 
v___x_2830_ = 92;
v_got_2831_ = lean_byte_array_fget(v_array_2824_, v_idx_2825_);
v___x_2832_ = lean_uint8_dec_eq(v_got_2831_, v___x_2830_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_2834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_a_2823_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
return v___x_2834_;
}
else
{
lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2868_; 
lean_inc(v_idx_2825_);
lean_inc_ref(v_array_2824_);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_a_2823_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; lean_object* v_unused_2870_; 
v_unused_2869_ = lean_ctor_get(v_a_2823_, 1);
lean_dec(v_unused_2869_);
v_unused_2870_ = lean_ctor_get(v_a_2823_, 0);
lean_dec(v_unused_2870_);
v___x_2836_ = v_a_2823_;
v_isShared_2837_ = v_isSharedCheck_2868_;
goto v_resetjp_2835_;
}
else
{
lean_dec(v_a_2823_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2868_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2838_ = lean_unsigned_to_nat(1u);
v___x_2839_ = lean_nat_add(v_idx_2825_, v___x_2838_);
lean_dec(v_idx_2825_);
v___x_2840_ = lean_nat_dec_lt(v___x_2839_, v___x_2826_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2842_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 1, v___x_2839_);
v___x_2842_ = v___x_2836_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_array_2824_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___x_2839_);
v___x_2842_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
return v___x_2844_;
}
}
else
{
uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2846_ = lean_byte_array_fget(v_array_2824_, v___x_2839_);
v___x_2847_ = lean_nat_add(v___x_2839_, v___x_2838_);
lean_dec(v___x_2839_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 1, v___x_2847_);
v___x_2849_ = v___x_2836_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_array_2824_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint32_t v___x_2852_; uint32_t v___x_2859_; uint8_t v___x_2860_; 
v___x_2850_ = lean_box(v___x_2846_);
lean_inc_ref(v___x_2849_);
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = lean_uint8_to_uint32(v___x_2846_);
v___x_2859_ = 9;
v___x_2860_ = lean_uint32_dec_eq(v___x_2852_, v___x_2859_);
if (v___x_2860_ == 0)
{
uint32_t v___x_2861_; uint8_t v___x_2862_; 
v___x_2861_ = 32;
v___x_2862_ = lean_uint32_dec_eq(v___x_2852_, v___x_2861_);
if (v___x_2862_ == 0)
{
uint32_t v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = 33;
v___x_2864_ = lean_uint32_dec_le(v___x_2863_, v___x_2852_);
if (v___x_2864_ == 0)
{
lean_dec_ref_known(v___x_2851_, 2);
goto v___jp_2853_;
}
else
{
uint32_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = 126;
v___x_2866_ = lean_uint32_dec_le(v___x_2852_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_dec_ref_known(v___x_2851_, 2);
goto v___jp_2853_;
}
else
{
lean_dec_ref(v___x_2849_);
return v___x_2851_;
}
}
}
else
{
lean_dec_ref(v___x_2849_);
return v___x_2851_;
}
}
else
{
lean_dec_ref(v___x_2849_);
return v___x_2851_;
}
v___jp_2853_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2854_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2855_ = l_Char_quote(v___x_2852_);
v___x_2856_ = lean_string_append(v___x_2854_, v___x_2855_);
lean_dec_ref(v___x_2855_);
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2849_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
return v___x_2858_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2875_, lean_object* v_buf_2876_, lean_object* v_length_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_array_2879_; lean_object* v_idx_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; 
v_array_2879_ = lean_ctor_get(v_a_2878_, 0);
v_idx_2880_ = lean_ctor_get(v_a_2878_, 1);
v___x_2881_ = lean_byte_array_size(v_array_2879_);
v___x_2882_ = lean_nat_dec_lt(v_idx_2880_, v___x_2881_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec(v_length_2877_);
lean_dec_ref(v_buf_2876_);
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_a_2878_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
return v___x_2884_;
}
else
{
lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2957_; 
lean_inc(v_idx_2880_);
lean_inc_ref(v_array_2879_);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_a_2878_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; lean_object* v_unused_2959_; 
v_unused_2958_ = lean_ctor_get(v_a_2878_, 1);
lean_dec(v_unused_2958_);
v_unused_2959_ = lean_ctor_get(v_a_2878_, 0);
lean_dec(v_unused_2959_);
v___x_2886_ = v_a_2878_;
v_isShared_2887_ = v_isSharedCheck_2957_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v_a_2878_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2957_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
uint8_t v_c_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v_it_x27_2892_; 
v_c_2888_ = lean_byte_array_fget(v_array_2879_, v_idx_2880_);
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_add(v_idx_2880_, v___x_2889_);
lean_dec(v_idx_2880_);
lean_inc(v___x_2890_);
lean_inc_ref(v_array_2879_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 1, v___x_2890_);
v_it_x27_2892_ = v___x_2886_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_array_2879_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v___x_2890_);
v_it_x27_2892_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
uint8_t v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = 34;
v___x_2908_ = lean_uint8_dec_eq(v_c_2888_, v___x_2907_);
if (v___x_2908_ == 0)
{
uint8_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = 92;
v___x_2910_ = lean_uint8_dec_eq(v_c_2888_, v___x_2909_);
if (v___x_2910_ == 0)
{
uint32_t v___x_2911_; uint32_t v___x_2917_; uint8_t v___x_2918_; 
lean_dec(v___x_2890_);
lean_dec_ref(v_array_2879_);
v___x_2911_ = lean_uint8_to_uint32(v_c_2888_);
v___x_2917_ = 9;
v___x_2918_ = lean_uint32_dec_eq(v___x_2911_, v___x_2917_);
if (v___x_2918_ == 0)
{
uint32_t v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = 32;
v___x_2920_ = lean_uint32_dec_eq(v___x_2911_, v___x_2919_);
if (v___x_2920_ == 0)
{
uint32_t v___x_2921_; uint8_t v___x_2922_; 
v___x_2921_ = 33;
v___x_2922_ = lean_uint32_dec_eq(v___x_2911_, v___x_2921_);
if (v___x_2922_ == 0)
{
uint32_t v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = 35;
v___x_2924_ = lean_uint32_dec_le(v___x_2923_, v___x_2911_);
if (v___x_2924_ == 0)
{
goto v___jp_2912_;
}
else
{
uint32_t v___x_2925_; uint8_t v___x_2926_; 
v___x_2925_ = 91;
v___x_2926_ = lean_uint32_dec_le(v___x_2911_, v___x_2925_);
if (v___x_2926_ == 0)
{
goto v___jp_2912_;
}
else
{
goto v___jp_2893_;
}
}
}
else
{
goto v___jp_2893_;
}
}
else
{
goto v___jp_2893_;
}
}
else
{
goto v___jp_2893_;
}
v___jp_2912_:
{
uint32_t v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = 93;
v___x_2914_ = lean_uint32_dec_le(v___x_2913_, v___x_2911_);
if (v___x_2914_ == 0)
{
lean_dec(v_length_2877_);
lean_dec_ref(v_buf_2876_);
goto v___jp_2900_;
}
else
{
uint32_t v___x_2915_; uint8_t v___x_2916_; 
v___x_2915_ = 126;
v___x_2916_ = lean_uint32_dec_le(v___x_2911_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_dec(v_length_2877_);
lean_dec_ref(v_buf_2876_);
goto v___jp_2900_;
}
else
{
goto v___jp_2893_;
}
}
}
}
else
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_nat_dec_lt(v___x_2890_, v___x_2881_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec(v___x_2890_);
lean_dec_ref(v_array_2879_);
lean_dec(v_length_2877_);
lean_dec_ref(v_buf_2876_);
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2929_, 0, v_it_x27_2892_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
return v___x_2929_;
}
else
{
uint8_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; uint32_t v___x_2940_; uint32_t v___x_2947_; uint8_t v___x_2948_; 
lean_dec_ref(v_it_x27_2892_);
v___x_2930_ = lean_byte_array_fget(v_array_2879_, v___x_2890_);
v___x_2931_ = lean_nat_add(v___x_2890_, v___x_2889_);
lean_dec(v___x_2890_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v_array_2879_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2940_ = lean_uint8_to_uint32(v___x_2930_);
v___x_2947_ = 9;
v___x_2948_ = lean_uint32_dec_eq(v___x_2940_, v___x_2947_);
if (v___x_2948_ == 0)
{
uint32_t v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = 32;
v___x_2950_ = lean_uint32_dec_eq(v___x_2940_, v___x_2949_);
if (v___x_2950_ == 0)
{
uint32_t v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = 33;
v___x_2952_ = lean_uint32_dec_le(v___x_2951_, v___x_2940_);
if (v___x_2952_ == 0)
{
lean_dec(v_length_2877_);
lean_dec_ref(v_buf_2876_);
goto v___jp_2941_;
}
else
{
uint32_t v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = 126;
v___x_2954_ = lean_uint32_dec_le(v___x_2940_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec(v_length_2877_);
lean_dec_ref(v_buf_2876_);
goto v___jp_2941_;
}
else
{
goto v___jp_2933_;
}
}
}
else
{
goto v___jp_2933_;
}
}
else
{
goto v___jp_2933_;
}
v___jp_2933_:
{
lean_object* v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = lean_nat_add(v_length_2877_, v___x_2889_);
lean_dec(v_length_2877_);
v___x_2935_ = lean_nat_dec_lt(v_maxLength_2875_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_byte_array_push(v_buf_2876_, v___x_2930_);
v_buf_2876_ = v___x_2936_;
v_length_2877_ = v___x_2934_;
v_a_2878_ = v___x_2932_;
goto _start;
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec(v___x_2934_);
lean_dec_ref(v_buf_2876_);
v___x_2938_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2932_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
return v___x_2939_;
}
}
v___jp_2941_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2942_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2943_ = l_Char_quote(v___x_2940_);
v___x_2944_ = lean_string_append(v___x_2942_, v___x_2943_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2932_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
return v___x_2946_;
}
}
}
}
else
{
lean_object* v___x_2955_; 
lean_dec(v___x_2890_);
lean_dec_ref(v_array_2879_);
lean_dec(v_length_2877_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_it_x27_2892_);
lean_ctor_set(v___x_2955_, 1, v_buf_2876_);
return v___x_2955_;
}
v___jp_2893_:
{
lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2894_ = lean_nat_add(v_length_2877_, v___x_2889_);
lean_dec(v_length_2877_);
v___x_2895_ = lean_nat_dec_lt(v_maxLength_2875_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_byte_array_push(v_buf_2876_, v_c_2888_);
v_buf_2876_ = v___x_2896_;
v_length_2877_ = v___x_2894_;
v_a_2878_ = v_it_x27_2892_;
goto _start;
}
else
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec(v___x_2894_);
lean_dec_ref(v_buf_2876_);
v___x_2898_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_it_x27_2892_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
return v___x_2899_;
}
}
v___jp_2900_:
{
lean_object* v___x_2901_; uint32_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2901_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2902_ = lean_uint8_to_uint32(v_c_2888_);
v___x_2903_ = l_Char_quote(v___x_2902_);
v___x_2904_ = lean_string_append(v___x_2901_, v___x_2903_);
lean_dec_ref(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
v___x_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2906_, 0, v_it_x27_2892_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
return v___x_2906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2960_, lean_object* v_buf_2961_, lean_object* v_length_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2960_, v_buf_2961_, v_length_2962_, v_a_2963_);
lean_dec(v_maxLength_2960_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_array_2970_; lean_object* v_idx_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_array_2970_ = lean_ctor_get(v_a_2969_, 0);
v_idx_2971_ = lean_ctor_get(v_a_2969_, 1);
v___x_2972_ = lean_byte_array_size(v_array_2970_);
v___x_2973_ = lean_nat_dec_lt(v_idx_2971_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2975_, 0, v_a_2969_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
return v___x_2975_;
}
else
{
uint8_t v___x_2976_; uint8_t v_got_2977_; uint8_t v___x_2978_; 
v___x_2976_ = 34;
v_got_2977_ = lean_byte_array_fget(v_array_2970_, v_idx_2971_);
v___x_2978_ = lean_uint8_dec_eq(v_got_2977_, v___x_2976_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2980_, 0, v_a_2969_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
return v___x_2980_;
}
else
{
lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3009_; 
lean_inc(v_idx_2971_);
lean_inc_ref(v_array_2970_);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_a_2969_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; lean_object* v_unused_3011_; 
v_unused_3010_ = lean_ctor_get(v_a_2969_, 1);
lean_dec(v_unused_3010_);
v_unused_3011_ = lean_ctor_get(v_a_2969_, 0);
lean_dec(v_unused_3011_);
v___x_2982_ = v_a_2969_;
v_isShared_2983_ = v_isSharedCheck_3009_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v_a_2969_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3009_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2984_ = lean_unsigned_to_nat(1u);
v___x_2985_ = lean_nat_add(v_idx_2971_, v___x_2984_);
lean_dec(v_idx_2971_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 1, v___x_2985_);
v___x_2987_ = v___x_2982_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_array_2970_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = l_ByteArray_empty;
v___x_2989_ = lean_unsigned_to_nat(0u);
v___x_2990_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2968_, v___x_2988_, v___x_2989_, v___x_2987_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_pos_2991_; lean_object* v_res_2992_; uint8_t v___x_2993_; 
v_pos_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_pos_2991_);
v_res_2992_ = lean_ctor_get(v___x_2990_, 1);
lean_inc(v_res_2992_);
lean_dec_ref_known(v___x_2990_, 2);
v___x_2993_ = lean_string_validate_utf8(v_res_2992_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec(v_res_2992_);
v___x_2994_ = lean_box(0);
v___x_2995_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2994_, v_pos_2991_);
return v___x_2995_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_string_from_utf8_unchecked(v_res_2992_);
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2997_, v_pos_2991_);
lean_dec_ref_known(v___x_2997_, 1);
return v___x_2998_;
}
}
else
{
lean_object* v_pos_2999_; lean_object* v_err_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v_pos_2999_ = lean_ctor_get(v___x_2990_, 0);
v_err_3000_ = lean_ctor_get(v___x_2990_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2990_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_err_3000_);
lean_inc(v_pos_2999_);
lean_dec(v___x_2990_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_pos_2999_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_err_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_3012_, v_a_3013_);
lean_dec(v_maxLength_3012_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_3015_, lean_object* v_maxSpaceSequence_3016_, lean_object* v_x_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_pos_3020_; lean_object* v_pos_3024_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_snd_3029_; lean_object* v_snd_3030_; uint8_t v___x_3031_; 
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3015_, v_maxSpaceSequence_3016_, v___x_3027_, v___y_3018_);
v_snd_3029_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_snd_3029_);
lean_dec_ref(v___x_3028_);
v_snd_3030_ = lean_ctor_get(v_snd_3029_, 1);
v___x_3031_ = lean_unbox(v_snd_3030_);
if (v___x_3031_ == 0)
{
lean_object* v_fst_3032_; lean_object* v_array_3033_; lean_object* v_idx_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_fst_3032_ = lean_ctor_get(v_snd_3029_, 0);
lean_inc(v_fst_3032_);
lean_dec(v_snd_3029_);
v_array_3033_ = lean_ctor_get(v_fst_3032_, 0);
v_idx_3034_ = lean_ctor_get(v_fst_3032_, 1);
v___x_3035_ = lean_byte_array_size(v_array_3033_);
v___x_3036_ = lean_nat_dec_lt(v_idx_3034_, v___x_3035_);
if (v___x_3036_ == 0)
{
v_pos_3020_ = v_fst_3032_;
goto v___jp_3019_;
}
else
{
uint8_t v___x_3037_; uint32_t v___x_3038_; uint32_t v___x_3039_; uint8_t v___x_3040_; 
v___x_3037_ = lean_byte_array_fget(v_array_3033_, v_idx_3034_);
v___x_3038_ = lean_uint8_to_uint32(v___x_3037_);
v___x_3039_ = 32;
v___x_3040_ = lean_uint32_dec_eq(v___x_3038_, v___x_3039_);
if (v___x_3040_ == 0)
{
uint32_t v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = 9;
v___x_3042_ = lean_uint32_dec_eq(v___x_3038_, v___x_3041_);
if (v___x_3042_ == 0)
{
v_pos_3020_ = v_fst_3032_;
goto v___jp_3019_;
}
else
{
v_pos_3024_ = v_fst_3032_;
goto v___jp_3023_;
}
}
else
{
v_pos_3024_ = v_fst_3032_;
goto v___jp_3023_;
}
}
}
else
{
lean_object* v_fst_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
v_fst_3043_ = lean_ctor_get(v_snd_3029_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_snd_3029_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v_snd_3029_, 1);
lean_dec(v_unused_3052_);
v___x_3045_ = v_snd_3029_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_fst_3043_);
lean_dec(v_snd_3029_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = lean_box(0);
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 1);
lean_ctor_set(v___x_3045_, 1, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_fst_3043_);
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
v___jp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_pos_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
return v___x_3022_;
}
v___jp_3023_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v_pos_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_3053_, lean_object* v_maxSpaceSequence_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3053_, v_maxSpaceSequence_3054_, v_x_3055_, v___y_3056_);
lean_dec(v_maxSpaceSequence_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_pos_3073_; lean_object* v_pos_3077_; lean_object* v___y_3081_; lean_object* v_pos_3082_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3114_; lean_object* v_pos_3115_; lean_object* v_res_3116_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v_lower_3122_; lean_object* v_upper_3123_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v_pos_3139_; lean_object* v_pos_3143_; lean_object* v_maxSpaceSequence_3146_; lean_object* v_maxChunkExtNameLength_3147_; lean_object* v_maxChunkExtValueLength_3148_; lean_object* v___f_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_snd_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3440_; 
v_maxSpaceSequence_3146_ = lean_ctor_get(v_limits_3070_, 8);
v_maxChunkExtNameLength_3147_ = lean_ctor_get(v_limits_3070_, 11);
v_maxChunkExtValueLength_3148_ = lean_ctor_get(v_limits_3070_, 12);
v___f_3149_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3149_, v_maxSpaceSequence_3146_, v___x_3150_, v_a_3071_);
v_snd_3152_ = lean_ctor_get(v___x_3151_, 1);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3440_ == 0)
{
lean_object* v_unused_3441_; 
v_unused_3441_ = lean_ctor_get(v___x_3151_, 0);
lean_dec(v_unused_3441_);
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3440_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snd_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3440_;
goto v_resetjp_3153_;
}
v___jp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3075_, 0, v_pos_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
return v___x_3075_;
}
v___jp_3076_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3079_, 0, v_pos_3077_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
return v___x_3079_;
}
v___jp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_box(0);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___y_3081_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_pos_3082_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
return v___x_3085_;
}
v___jp_3086_:
{
if (lean_obj_tag(v___y_3088_) == 0)
{
lean_object* v_pos_3089_; lean_object* v_res_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3103_; 
v_pos_3089_ = lean_ctor_get(v___y_3088_, 0);
v_res_3090_ = lean_ctor_get(v___y_3088_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___y_3088_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3092_ = v___y_3088_;
v_isShared_3093_ = v_isSharedCheck_3103_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_res_3090_);
lean_inc(v_pos_3089_);
lean_dec(v___y_3088_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3103_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_3090_);
if (lean_obj_tag(v___x_3094_) == 1)
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___y_3087_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v___x_3095_);
v___x_3097_ = v___x_3092_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_pos_3089_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
lean_dec(v___x_3094_);
lean_dec_ref(v___y_3087_);
v___x_3099_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_3093_ == 0)
{
lean_ctor_set_tag(v___x_3092_, 1);
lean_ctor_set(v___x_3092_, 1, v___x_3099_);
v___x_3101_ = v___x_3092_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_pos_3089_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_pos_3104_; lean_object* v_err_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref(v___y_3087_);
v_pos_3104_ = lean_ctor_get(v___y_3088_, 0);
v_err_3105_ = lean_ctor_get(v___y_3088_, 1);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___y_3088_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___y_3088_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_err_3105_);
lean_inc(v_pos_3104_);
lean_dec(v___y_3088_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_pos_3104_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_err_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
v___jp_3113_:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3116_, v_pos_3115_);
lean_dec(v_res_3116_);
v___y_3087_ = v___y_3114_;
v___y_3088_ = v___x_3117_;
goto v___jp_3086_;
}
v___jp_3118_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3124_ = l_ByteArray_toByteSlice(v___y_3120_, v_lower_3122_, v_upper_3123_);
v___x_3125_ = l_ByteSlice_toByteArray(v___x_3124_);
v___x_3126_ = lean_string_validate_utf8(v___x_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_dec_ref(v___x_3125_);
v___x_3127_ = lean_box(0);
v___y_3114_ = v___y_3119_;
v_pos_3115_ = v___y_3121_;
v_res_3116_ = v___x_3127_;
goto v___jp_3113_;
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_string_from_utf8_unchecked(v___x_3125_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
v___y_3114_ = v___y_3119_;
v_pos_3115_ = v___y_3121_;
v_res_3116_ = v___x_3129_;
goto v___jp_3113_;
}
}
v___jp_3130_:
{
uint8_t v___x_3137_; 
v___x_3137_ = lean_nat_dec_le(v___y_3131_, v___y_3134_);
if (v___x_3137_ == 0)
{
lean_dec(v___y_3131_);
v___y_3119_ = v___y_3132_;
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3135_;
v_lower_3122_ = v___y_3136_;
v_upper_3123_ = v___y_3134_;
goto v___jp_3118_;
}
else
{
lean_dec(v___y_3134_);
v___y_3119_ = v___y_3132_;
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3135_;
v_lower_3122_ = v___y_3136_;
v_upper_3123_ = v___y_3131_;
goto v___jp_3118_;
}
}
v___jp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3141_, 0, v_pos_3139_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
return v___x_3141_;
}
v___jp_3142_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_pos_3143_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
return v___x_3145_;
}
v_resetjp_3153_:
{
lean_object* v_snd_3156_; uint8_t v___x_3157_; 
v_snd_3156_ = lean_ctor_get(v_snd_3152_, 1);
v___x_3157_ = lean_unbox(v_snd_3156_);
if (v___x_3157_ == 0)
{
lean_object* v_fst_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3428_; 
v_fst_3158_ = lean_ctor_get(v_snd_3152_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_snd_3152_);
if (v_isSharedCheck_3428_ == 0)
{
lean_object* v_unused_3429_; 
v_unused_3429_ = lean_ctor_get(v_snd_3152_, 1);
lean_dec(v_unused_3429_);
v___x_3160_ = v_snd_3152_;
v_isShared_3161_ = v_isSharedCheck_3428_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_fst_3158_);
lean_dec(v_snd_3152_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3428_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_array_3162_; lean_object* v_idx_3163_; lean_object* v___f_3164_; lean_object* v___y_3166_; lean_object* v_pos_3167_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v_pos_3202_; lean_object* v_array_3203_; lean_object* v_idx_3204_; lean_object* v_pos_3260_; lean_object* v_res_3261_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v_lower_3327_; lean_object* v_upper_3328_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v_pos_3343_; lean_object* v_pos_3376_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v_array_3162_ = lean_ctor_get(v_fst_3158_, 0);
v_idx_3163_ = lean_ctor_get(v_fst_3158_, 1);
v___f_3164_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_3420_ = lean_byte_array_size(v_array_3162_);
v___x_3421_ = lean_nat_dec_lt(v_idx_3163_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_inc(v_idx_3163_);
lean_inc_ref(v_array_3162_);
v_pos_3376_ = v_fst_3158_;
goto v___jp_3375_;
}
else
{
uint8_t v___x_3422_; uint32_t v___x_3423_; uint32_t v___x_3424_; uint8_t v___x_3425_; 
v___x_3422_ = lean_byte_array_fget(v_array_3162_, v_idx_3163_);
v___x_3423_ = lean_uint8_to_uint32(v___x_3422_);
v___x_3424_ = 32;
v___x_3425_ = lean_uint32_dec_eq(v___x_3423_, v___x_3424_);
if (v___x_3425_ == 0)
{
uint32_t v___x_3426_; uint8_t v___x_3427_; 
v___x_3426_ = 9;
v___x_3427_ = lean_uint32_dec_eq(v___x_3423_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_inc(v_idx_3163_);
lean_inc_ref(v_array_3162_);
v_pos_3376_ = v_fst_3158_;
goto v___jp_3375_;
}
else
{
lean_del_object(v___x_3160_);
lean_del_object(v___x_3154_);
v_pos_3073_ = v_fst_3158_;
goto v___jp_3072_;
}
}
else
{
lean_del_object(v___x_3160_);
lean_del_object(v___x_3154_);
v_pos_3073_ = v_fst_3158_;
goto v___jp_3072_;
}
}
v___jp_3165_:
{
lean_object* v___x_3168_; 
lean_inc_ref(v_pos_3167_);
v___x_3168_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_3148_, v_pos_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_dec_ref(v_pos_3167_);
v___y_3087_ = v___y_3166_;
v___y_3088_ = v___x_3168_;
goto v___jp_3086_;
}
else
{
lean_object* v_pos_3169_; lean_object* v_idx_3170_; lean_object* v_array_3171_; lean_object* v_idx_3172_; uint8_t v___x_3173_; 
v_pos_3169_ = lean_ctor_get(v___x_3168_, 0);
v_idx_3170_ = lean_ctor_get(v_pos_3167_, 1);
lean_inc(v_idx_3170_);
lean_dec_ref(v_pos_3167_);
v_array_3171_ = lean_ctor_get(v_pos_3169_, 0);
v_idx_3172_ = lean_ctor_get(v_pos_3169_, 1);
v___x_3173_ = lean_nat_dec_eq(v_idx_3170_, v_idx_3172_);
lean_dec(v_idx_3170_);
if (v___x_3173_ == 0)
{
v___y_3087_ = v___y_3166_;
v___y_3088_ = v___x_3168_;
goto v___jp_3086_;
}
else
{
lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3196_; 
lean_inc(v_pos_3169_);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; lean_object* v_unused_3198_; 
v_unused_3197_ = lean_ctor_get(v___x_3168_, 1);
lean_dec(v_unused_3197_);
v_unused_3198_ = lean_ctor_get(v___x_3168_, 0);
lean_dec(v_unused_3198_);
v___x_3175_ = v___x_3168_;
v_isShared_3176_ = v_isSharedCheck_3196_;
goto v_resetjp_3174_;
}
else
{
lean_dec(v___x_3168_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3196_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v_snd_3178_; lean_object* v_snd_3179_; uint8_t v___x_3180_; 
lean_inc(v_pos_3169_);
v___x_3177_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3164_, v_maxChunkExtValueLength_3148_, v___x_3150_, v_pos_3169_);
v_snd_3178_ = lean_ctor_get(v___x_3177_, 1);
lean_inc(v_snd_3178_);
v_snd_3179_ = lean_ctor_get(v_snd_3178_, 1);
v___x_3180_ = lean_unbox(v_snd_3179_);
if (v___x_3180_ == 0)
{
lean_object* v_fst_3181_; lean_object* v_fst_3182_; uint8_t v___x_3183_; 
v_fst_3181_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_fst_3181_);
lean_dec_ref(v___x_3177_);
v_fst_3182_ = lean_ctor_get(v_snd_3178_, 0);
lean_inc(v_fst_3182_);
lean_dec(v_snd_3178_);
v___x_3183_ = lean_nat_dec_eq(v_fst_3181_, v___x_3150_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
lean_inc(v_idx_3172_);
lean_inc_ref(v_array_3171_);
lean_del_object(v___x_3175_);
lean_dec(v_pos_3169_);
v___x_3184_ = lean_nat_add(v_idx_3172_, v_fst_3181_);
lean_dec(v_fst_3181_);
v___x_3185_ = lean_byte_array_size(v_array_3171_);
v___x_3186_ = lean_nat_dec_le(v_idx_3172_, v___x_3150_);
if (v___x_3186_ == 0)
{
v___y_3131_ = v___x_3184_;
v___y_3132_ = v___y_3166_;
v___y_3133_ = v_array_3171_;
v___y_3134_ = v___x_3185_;
v___y_3135_ = v_fst_3182_;
v___y_3136_ = v_idx_3172_;
goto v___jp_3130_;
}
else
{
lean_dec(v_idx_3172_);
v___y_3131_ = v___x_3184_;
v___y_3132_ = v___y_3166_;
v___y_3133_ = v_array_3171_;
v___y_3134_ = v___x_3185_;
v___y_3135_ = v_fst_3182_;
v___y_3136_ = v___x_3150_;
goto v___jp_3130_;
}
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
lean_dec(v_fst_3182_);
lean_dec(v_fst_3181_);
lean_dec_ref(v___y_3166_);
v___x_3187_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v___x_3187_);
v___x_3189_ = v___x_3175_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_pos_3169_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
else
{
lean_object* v_fst_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_dec_ref(v___x_3177_);
lean_dec(v_pos_3169_);
lean_dec_ref(v___y_3166_);
v_fst_3191_ = lean_ctor_get(v_snd_3178_, 0);
lean_inc(v_fst_3191_);
lean_dec(v_snd_3178_);
v___x_3192_ = lean_box(0);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v___x_3192_);
lean_ctor_set(v___x_3175_, 0, v_fst_3191_);
v___x_3194_ = v___x_3175_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_fst_3191_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
}
v___jp_3199_:
{
lean_object* v___x_3205_; uint8_t v___x_3206_; 
v___x_3205_ = lean_byte_array_size(v_array_3203_);
v___x_3206_ = lean_nat_dec_lt(v_idx_3204_, v___x_3205_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
lean_dec(v_idx_3204_);
lean_dec_ref(v_array_3203_);
lean_dec_ref(v___y_3200_);
v___x_3207_ = lean_box(0);
if (v_isShared_3161_ == 0)
{
lean_ctor_set_tag(v___x_3160_, 1);
lean_ctor_set(v___x_3160_, 1, v___x_3207_);
lean_ctor_set(v___x_3160_, 0, v_pos_3202_);
v___x_3209_ = v___x_3160_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_pos_3202_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
else
{
uint8_t v___x_3211_; uint8_t v_got_3212_; uint8_t v___x_3213_; 
v___x_3211_ = 61;
v_got_3212_ = lean_byte_array_fget(v_array_3203_, v_idx_3204_);
v___x_3213_ = lean_uint8_dec_eq(v_got_3212_, v___x_3211_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
lean_dec(v_idx_3204_);
lean_dec_ref(v_array_3203_);
lean_dec_ref(v___y_3200_);
v___x_3214_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_3161_ == 0)
{
lean_ctor_set_tag(v___x_3160_, 1);
lean_ctor_set(v___x_3160_, 1, v___x_3214_);
lean_ctor_set(v___x_3160_, 0, v_pos_3202_);
v___x_3216_ = v___x_3160_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_pos_3202_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_dec_ref(v_pos_3202_);
v___x_3218_ = lean_unsigned_to_nat(1u);
v___x_3219_ = lean_nat_add(v_idx_3204_, v___x_3218_);
lean_dec(v_idx_3204_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v___x_3219_);
lean_ctor_set(v___x_3160_, 0, v_array_3203_);
v___x_3221_ = v___x_3160_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_array_3203_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3149_, v_maxSpaceSequence_3146_, v___y_3201_, v___x_3221_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_pos_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3247_; 
v_pos_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v___x_3222_, 1);
lean_dec(v_unused_3248_);
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3247_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_pos_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3247_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v_snd_3228_; lean_object* v_snd_3229_; uint8_t v___x_3230_; 
v___x_3227_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3149_, v_maxSpaceSequence_3146_, v___x_3150_, v_pos_3223_);
v_snd_3228_ = lean_ctor_get(v___x_3227_, 1);
lean_inc(v_snd_3228_);
lean_dec_ref(v___x_3227_);
v_snd_3229_ = lean_ctor_get(v_snd_3228_, 1);
v___x_3230_ = lean_unbox(v_snd_3229_);
if (v___x_3230_ == 0)
{
lean_object* v_fst_3231_; lean_object* v_array_3232_; lean_object* v_idx_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
lean_del_object(v___x_3225_);
v_fst_3231_ = lean_ctor_get(v_snd_3228_, 0);
lean_inc(v_fst_3231_);
lean_dec(v_snd_3228_);
v_array_3232_ = lean_ctor_get(v_fst_3231_, 0);
v_idx_3233_ = lean_ctor_get(v_fst_3231_, 1);
v___x_3234_ = lean_byte_array_size(v_array_3232_);
v___x_3235_ = lean_nat_dec_lt(v_idx_3233_, v___x_3234_);
if (v___x_3235_ == 0)
{
v___y_3166_ = v___y_3200_;
v_pos_3167_ = v_fst_3231_;
goto v___jp_3165_;
}
else
{
uint8_t v___x_3236_; uint32_t v___x_3237_; uint32_t v___x_3238_; uint8_t v___x_3239_; 
v___x_3236_ = lean_byte_array_fget(v_array_3232_, v_idx_3233_);
v___x_3237_ = lean_uint8_to_uint32(v___x_3236_);
v___x_3238_ = 32;
v___x_3239_ = lean_uint32_dec_eq(v___x_3237_, v___x_3238_);
if (v___x_3239_ == 0)
{
uint32_t v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = 9;
v___x_3241_ = lean_uint32_dec_eq(v___x_3237_, v___x_3240_);
if (v___x_3241_ == 0)
{
v___y_3166_ = v___y_3200_;
v_pos_3167_ = v_fst_3231_;
goto v___jp_3165_;
}
else
{
lean_dec_ref(v___y_3200_);
v_pos_3139_ = v_fst_3231_;
goto v___jp_3138_;
}
}
else
{
lean_dec_ref(v___y_3200_);
v_pos_3139_ = v_fst_3231_;
goto v___jp_3138_;
}
}
}
else
{
lean_object* v_fst_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
lean_dec_ref(v___y_3200_);
v_fst_3242_ = lean_ctor_get(v_snd_3228_, 0);
lean_inc(v_fst_3242_);
lean_dec(v_snd_3228_);
v___x_3243_ = lean_box(0);
if (v_isShared_3226_ == 0)
{
lean_ctor_set_tag(v___x_3225_, 1);
lean_ctor_set(v___x_3225_, 1, v___x_3243_);
lean_ctor_set(v___x_3225_, 0, v_fst_3242_);
v___x_3245_ = v___x_3225_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_fst_3242_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_object* v_pos_3249_; lean_object* v_err_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v___y_3200_);
v_pos_3249_ = lean_ctor_get(v___x_3222_, 0);
v_err_3250_ = lean_ctor_get(v___x_3222_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3222_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_err_3250_);
lean_inc(v_pos_3249_);
lean_dec(v___x_3222_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_pos_3249_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_err_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
}
}
v___jp_3259_:
{
lean_object* v___x_3262_; 
v___x_3262_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3261_, v_pos_3260_);
lean_dec(v_res_3261_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_pos_3263_; lean_object* v_res_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v_pos_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_pos_3263_);
v_res_3264_ = lean_ctor_get(v___x_3262_, 1);
lean_inc(v_res_3264_);
lean_dec_ref_known(v___x_3262_, 2);
v___x_3265_ = lean_box(0);
v___x_3266_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3149_, v_maxSpaceSequence_3146_, v___x_3265_, v_pos_3263_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_pos_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3304_; 
v_pos_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3304_ == 0)
{
lean_object* v_unused_3305_; 
v_unused_3305_ = lean_ctor_get(v___x_3266_, 1);
lean_dec(v_unused_3305_);
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3304_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_pos_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3304_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_3264_);
if (lean_obj_tag(v___x_3271_) == 1)
{
lean_object* v_val_3272_; lean_object* v_array_3273_; lean_object* v_idx_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v_val_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_val_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v_array_3273_ = lean_ctor_get(v_pos_3267_, 0);
v_idx_3274_ = lean_ctor_get(v_pos_3267_, 1);
v___x_3275_ = lean_byte_array_size(v_array_3273_);
v___x_3276_ = lean_nat_dec_lt(v_idx_3274_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_del_object(v___x_3269_);
lean_del_object(v___x_3160_);
v___y_3081_ = v_val_3272_;
v_pos_3082_ = v_pos_3267_;
goto v___jp_3080_;
}
else
{
uint8_t v___x_3277_; uint8_t v___x_3278_; uint8_t v___x_3279_; 
v___x_3277_ = lean_byte_array_fget(v_array_3273_, v_idx_3274_);
v___x_3278_ = 61;
v___x_3279_ = lean_uint8_dec_eq(v___x_3277_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_del_object(v___x_3269_);
lean_del_object(v___x_3160_);
v___y_3081_ = v_val_3272_;
v_pos_3082_ = v_pos_3267_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3280_; lean_object* v_snd_3281_; lean_object* v_snd_3282_; uint8_t v___x_3283_; 
v___x_3280_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3149_, v_maxSpaceSequence_3146_, v___x_3150_, v_pos_3267_);
v_snd_3281_ = lean_ctor_get(v___x_3280_, 1);
lean_inc(v_snd_3281_);
lean_dec_ref(v___x_3280_);
v_snd_3282_ = lean_ctor_get(v_snd_3281_, 1);
v___x_3283_ = lean_unbox(v_snd_3282_);
if (v___x_3283_ == 0)
{
lean_object* v_fst_3284_; lean_object* v_array_3285_; lean_object* v_idx_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
lean_del_object(v___x_3269_);
v_fst_3284_ = lean_ctor_get(v_snd_3281_, 0);
lean_inc(v_fst_3284_);
lean_dec(v_snd_3281_);
v_array_3285_ = lean_ctor_get(v_fst_3284_, 0);
v_idx_3286_ = lean_ctor_get(v_fst_3284_, 1);
v___x_3287_ = lean_byte_array_size(v_array_3285_);
v___x_3288_ = lean_nat_dec_lt(v_idx_3286_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_inc(v_idx_3286_);
lean_inc_ref(v_array_3285_);
v___y_3200_ = v_val_3272_;
v___y_3201_ = v___x_3265_;
v_pos_3202_ = v_fst_3284_;
v_array_3203_ = v_array_3285_;
v_idx_3204_ = v_idx_3286_;
goto v___jp_3199_;
}
else
{
uint8_t v___x_3289_; uint32_t v___x_3290_; uint32_t v___x_3291_; uint8_t v___x_3292_; 
v___x_3289_ = lean_byte_array_fget(v_array_3285_, v_idx_3286_);
v___x_3290_ = lean_uint8_to_uint32(v___x_3289_);
v___x_3291_ = 32;
v___x_3292_ = lean_uint32_dec_eq(v___x_3290_, v___x_3291_);
if (v___x_3292_ == 0)
{
uint32_t v___x_3293_; uint8_t v___x_3294_; 
v___x_3293_ = 9;
v___x_3294_ = lean_uint32_dec_eq(v___x_3290_, v___x_3293_);
if (v___x_3294_ == 0)
{
lean_inc(v_idx_3286_);
lean_inc_ref(v_array_3285_);
v___y_3200_ = v_val_3272_;
v___y_3201_ = v___x_3265_;
v_pos_3202_ = v_fst_3284_;
v_array_3203_ = v_array_3285_;
v_idx_3204_ = v_idx_3286_;
goto v___jp_3199_;
}
else
{
lean_dec(v_val_3272_);
lean_del_object(v___x_3160_);
v_pos_3143_ = v_fst_3284_;
goto v___jp_3142_;
}
}
else
{
lean_dec(v_val_3272_);
lean_del_object(v___x_3160_);
v_pos_3143_ = v_fst_3284_;
goto v___jp_3142_;
}
}
}
else
{
lean_object* v_fst_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
lean_dec(v_val_3272_);
lean_del_object(v___x_3160_);
v_fst_3295_ = lean_ctor_get(v_snd_3281_, 0);
lean_inc(v_fst_3295_);
lean_dec(v_snd_3281_);
v___x_3296_ = lean_box(0);
if (v_isShared_3270_ == 0)
{
lean_ctor_set_tag(v___x_3269_, 1);
lean_ctor_set(v___x_3269_, 1, v___x_3296_);
lean_ctor_set(v___x_3269_, 0, v_fst_3295_);
v___x_3298_ = v___x_3269_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_fst_3295_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
lean_dec(v___x_3271_);
lean_del_object(v___x_3160_);
v___x_3300_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
if (v_isShared_3270_ == 0)
{
lean_ctor_set_tag(v___x_3269_, 1);
lean_ctor_set(v___x_3269_, 1, v___x_3300_);
v___x_3302_ = v___x_3269_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_pos_3267_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_object* v_pos_3306_; lean_object* v_err_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_res_3264_);
lean_del_object(v___x_3160_);
v_pos_3306_ = lean_ctor_get(v___x_3266_, 0);
v_err_3307_ = lean_ctor_get(v___x_3266_, 1);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3266_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_err_3307_);
lean_inc(v_pos_3306_);
lean_dec(v___x_3266_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_pos_3306_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_err_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
else
{
lean_object* v_pos_3315_; lean_object* v_err_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_del_object(v___x_3160_);
v_pos_3315_ = lean_ctor_get(v___x_3262_, 0);
v_err_3316_ = lean_ctor_get(v___x_3262_, 1);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3262_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_err_3316_);
lean_inc(v_pos_3315_);
lean_dec(v___x_3262_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_pos_3315_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_err_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
v___jp_3324_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3329_ = l_ByteArray_toByteSlice(v___y_3326_, v_lower_3327_, v_upper_3328_);
v___x_3330_ = l_ByteSlice_toByteArray(v___x_3329_);
v___x_3331_ = lean_string_validate_utf8(v___x_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; 
lean_dec_ref(v___x_3330_);
v___x_3332_ = lean_box(0);
v_pos_3260_ = v___y_3325_;
v_res_3261_ = v___x_3332_;
goto v___jp_3259_;
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_string_from_utf8_unchecked(v___x_3330_);
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
v_pos_3260_ = v___y_3325_;
v_res_3261_ = v___x_3334_;
goto v___jp_3259_;
}
}
v___jp_3335_:
{
uint8_t v___x_3341_; 
v___x_3341_ = lean_nat_dec_le(v___y_3336_, v___y_3338_);
if (v___x_3341_ == 0)
{
lean_dec(v___y_3336_);
v___y_3325_ = v___y_3337_;
v___y_3326_ = v___y_3339_;
v_lower_3327_ = v___y_3340_;
v_upper_3328_ = v___y_3338_;
goto v___jp_3324_;
}
else
{
lean_dec(v___y_3338_);
v___y_3325_ = v___y_3337_;
v___y_3326_ = v___y_3339_;
v_lower_3327_ = v___y_3340_;
v_upper_3328_ = v___y_3336_;
goto v___jp_3324_;
}
}
v___jp_3342_:
{
lean_object* v___x_3344_; lean_object* v_snd_3345_; lean_object* v_snd_3346_; uint8_t v___x_3347_; 
lean_inc_ref(v_pos_3343_);
v___x_3344_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3164_, v_maxChunkExtNameLength_3147_, v___x_3150_, v_pos_3343_);
v_snd_3345_ = lean_ctor_get(v___x_3344_, 1);
lean_inc(v_snd_3345_);
v_snd_3346_ = lean_ctor_get(v_snd_3345_, 1);
v___x_3347_ = lean_unbox(v_snd_3346_);
if (v___x_3347_ == 0)
{
lean_object* v_fst_3348_; lean_object* v_fst_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3363_; 
v_fst_3348_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_fst_3348_);
lean_dec_ref(v___x_3344_);
v_fst_3349_ = lean_ctor_get(v_snd_3345_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_snd_3345_);
if (v_isSharedCheck_3363_ == 0)
{
lean_object* v_unused_3364_; 
v_unused_3364_ = lean_ctor_get(v_snd_3345_, 1);
lean_dec(v_unused_3364_);
v___x_3351_ = v_snd_3345_;
v_isShared_3352_ = v_isSharedCheck_3363_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_fst_3349_);
lean_dec(v_snd_3345_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3363_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_nat_dec_eq(v_fst_3348_, v___x_3150_);
if (v___x_3353_ == 0)
{
lean_object* v_array_3354_; lean_object* v_idx_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
lean_del_object(v___x_3351_);
v_array_3354_ = lean_ctor_get(v_pos_3343_, 0);
lean_inc_ref(v_array_3354_);
v_idx_3355_ = lean_ctor_get(v_pos_3343_, 1);
lean_inc(v_idx_3355_);
lean_dec_ref(v_pos_3343_);
v___x_3356_ = lean_nat_add(v_idx_3355_, v_fst_3348_);
lean_dec(v_fst_3348_);
v___x_3357_ = lean_byte_array_size(v_array_3354_);
v___x_3358_ = lean_nat_dec_le(v_idx_3355_, v___x_3150_);
if (v___x_3358_ == 0)
{
v___y_3336_ = v___x_3356_;
v___y_3337_ = v_fst_3349_;
v___y_3338_ = v___x_3357_;
v___y_3339_ = v_array_3354_;
v___y_3340_ = v_idx_3355_;
goto v___jp_3335_;
}
else
{
lean_dec(v_idx_3355_);
v___y_3336_ = v___x_3356_;
v___y_3337_ = v_fst_3349_;
v___y_3338_ = v___x_3357_;
v___y_3339_ = v_array_3354_;
v___y_3340_ = v___x_3150_;
goto v___jp_3335_;
}
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3361_; 
lean_dec(v_fst_3349_);
lean_dec(v_fst_3348_);
lean_del_object(v___x_3160_);
v___x_3359_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 1);
lean_ctor_set(v___x_3351_, 1, v___x_3359_);
lean_ctor_set(v___x_3351_, 0, v_pos_3343_);
v___x_3361_ = v___x_3351_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_pos_3343_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
else
{
lean_object* v_fst_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3373_; 
lean_dec_ref(v___x_3344_);
lean_dec_ref(v_pos_3343_);
lean_del_object(v___x_3160_);
v_fst_3365_ = lean_ctor_get(v_snd_3345_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v_snd_3345_);
if (v_isSharedCheck_3373_ == 0)
{
lean_object* v_unused_3374_; 
v_unused_3374_ = lean_ctor_get(v_snd_3345_, 1);
lean_dec(v_unused_3374_);
v___x_3367_ = v_snd_3345_;
v_isShared_3368_ = v_isSharedCheck_3373_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_fst_3365_);
lean_dec(v_snd_3345_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3373_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3369_ = lean_box(0);
if (v_isShared_3368_ == 0)
{
lean_ctor_set_tag(v___x_3367_, 1);
lean_ctor_set(v___x_3367_, 1, v___x_3369_);
v___x_3371_ = v___x_3367_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_fst_3365_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
v___jp_3375_:
{
lean_object* v___x_3377_; uint8_t v___x_3378_; 
v___x_3377_ = lean_byte_array_size(v_array_3162_);
v___x_3378_ = lean_nat_dec_lt(v_idx_3163_, v___x_3377_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3381_; 
lean_dec(v_idx_3163_);
lean_dec_ref(v_array_3162_);
lean_del_object(v___x_3160_);
v___x_3379_ = lean_box(0);
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 1);
lean_ctor_set(v___x_3154_, 1, v___x_3379_);
lean_ctor_set(v___x_3154_, 0, v_pos_3376_);
v___x_3381_ = v___x_3154_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_pos_3376_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
else
{
uint8_t v___x_3383_; uint8_t v_got_3384_; uint8_t v___x_3385_; 
v___x_3383_ = 59;
v_got_3384_ = lean_byte_array_fget(v_array_3162_, v_idx_3163_);
v___x_3385_ = lean_uint8_dec_eq(v_got_3384_, v___x_3383_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
lean_dec(v_idx_3163_);
lean_dec_ref(v_array_3162_);
lean_del_object(v___x_3160_);
v___x_3386_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7));
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 1);
lean_ctor_set(v___x_3154_, 1, v___x_3386_);
lean_ctor_set(v___x_3154_, 0, v_pos_3376_);
v___x_3388_ = v___x_3154_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_pos_3376_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
lean_dec_ref(v_pos_3376_);
v___x_3390_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_nat_add(v_idx_3163_, v___x_3390_);
lean_dec(v_idx_3163_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 1, v___x_3391_);
lean_ctor_set(v___x_3154_, 0, v_array_3162_);
v___x_3393_ = v___x_3154_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_array_3162_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
lean_object* v___x_3394_; lean_object* v_snd_3395_; lean_object* v_snd_3396_; uint8_t v___x_3397_; 
v___x_3394_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3149_, v_maxSpaceSequence_3146_, v___x_3150_, v___x_3393_);
v_snd_3395_ = lean_ctor_get(v___x_3394_, 1);
lean_inc(v_snd_3395_);
lean_dec_ref(v___x_3394_);
v_snd_3396_ = lean_ctor_get(v_snd_3395_, 1);
v___x_3397_ = lean_unbox(v_snd_3396_);
if (v___x_3397_ == 0)
{
lean_object* v_fst_3398_; lean_object* v_array_3399_; lean_object* v_idx_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v_fst_3398_ = lean_ctor_get(v_snd_3395_, 0);
lean_inc(v_fst_3398_);
lean_dec(v_snd_3395_);
v_array_3399_ = lean_ctor_get(v_fst_3398_, 0);
v_idx_3400_ = lean_ctor_get(v_fst_3398_, 1);
v___x_3401_ = lean_byte_array_size(v_array_3399_);
v___x_3402_ = lean_nat_dec_lt(v_idx_3400_, v___x_3401_);
if (v___x_3402_ == 0)
{
v_pos_3343_ = v_fst_3398_;
goto v___jp_3342_;
}
else
{
uint8_t v___x_3403_; uint32_t v___x_3404_; uint32_t v___x_3405_; uint8_t v___x_3406_; 
v___x_3403_ = lean_byte_array_fget(v_array_3399_, v_idx_3400_);
v___x_3404_ = lean_uint8_to_uint32(v___x_3403_);
v___x_3405_ = 32;
v___x_3406_ = lean_uint32_dec_eq(v___x_3404_, v___x_3405_);
if (v___x_3406_ == 0)
{
uint32_t v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = 9;
v___x_3408_ = lean_uint32_dec_eq(v___x_3404_, v___x_3407_);
if (v___x_3408_ == 0)
{
v_pos_3343_ = v_fst_3398_;
goto v___jp_3342_;
}
else
{
lean_del_object(v___x_3160_);
v_pos_3077_ = v_fst_3398_;
goto v___jp_3076_;
}
}
else
{
lean_del_object(v___x_3160_);
v_pos_3077_ = v_fst_3398_;
goto v___jp_3076_;
}
}
}
else
{
lean_object* v_fst_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3417_; 
lean_del_object(v___x_3160_);
v_fst_3409_ = lean_ctor_get(v_snd_3395_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_snd_3395_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v_snd_3395_, 1);
lean_dec(v_unused_3418_);
v___x_3411_ = v_snd_3395_;
v_isShared_3412_ = v_isSharedCheck_3417_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_fst_3409_);
lean_dec(v_snd_3395_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3417_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 1);
lean_ctor_set(v___x_3411_, 1, v___x_3413_);
v___x_3415_ = v___x_3411_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_fst_3409_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
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
lean_object* v_fst_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3438_; 
lean_del_object(v___x_3154_);
v_fst_3430_ = lean_ctor_get(v_snd_3152_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_snd_3152_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; 
v_unused_3439_ = lean_ctor_get(v_snd_3152_, 1);
lean_dec(v_unused_3439_);
v___x_3432_ = v_snd_3152_;
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_fst_3430_);
lean_dec(v_snd_3152_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3434_ = lean_box(0);
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 1);
lean_ctor_set(v___x_3432_, 1, v___x_3434_);
v___x_3436_ = v___x_3432_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_fst_3430_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3442_, v_a_3443_);
lean_dec_ref(v_limits_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v_pos_3448_; lean_object* v_err_3449_; lean_object* v___x_3465_; 
lean_inc_ref(v___y_3446_);
v___x_3465_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3445_, v___y_3446_);
if (lean_obj_tag(v___x_3465_) == 0)
{
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_pos_3466_; lean_object* v_res_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref(v___y_3446_);
v_pos_3466_ = lean_ctor_get(v___x_3465_, 0);
v_res_3467_ = lean_ctor_get(v___x_3465_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3469_ = v___x_3465_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_res_3467_);
lean_inc(v_pos_3466_);
lean_dec(v___x_3465_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v_res_3467_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 1, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_pos_3466_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
else
{
lean_object* v_pos_3476_; lean_object* v_err_3477_; 
v_pos_3476_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_pos_3476_);
v_err_3477_ = lean_ctor_get(v___x_3465_, 1);
lean_inc(v_err_3477_);
lean_dec_ref_known(v___x_3465_, 2);
v_pos_3448_ = v_pos_3476_;
v_err_3449_ = v_err_3477_;
goto v___jp_3447_;
}
}
else
{
lean_object* v_err_3478_; 
v_err_3478_ = lean_ctor_get(v___x_3465_, 1);
lean_inc(v_err_3478_);
lean_dec_ref_known(v___x_3465_, 2);
lean_inc_ref(v___y_3446_);
v_pos_3448_ = v___y_3446_;
v_err_3449_ = v_err_3478_;
goto v___jp_3447_;
}
v___jp_3447_:
{
lean_object* v_idx_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3463_; 
v_idx_3450_ = lean_ctor_get(v___y_3446_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___y_3446_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v___y_3446_, 0);
lean_dec(v_unused_3464_);
v___x_3452_ = v___y_3446_;
v_isShared_3453_ = v_isSharedCheck_3463_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_idx_3450_);
lean_dec(v___y_3446_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3463_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_idx_3454_; uint8_t v___x_3455_; 
v_idx_3454_ = lean_ctor_get(v_pos_3448_, 1);
v___x_3455_ = lean_nat_dec_eq(v_idx_3450_, v_idx_3454_);
lean_dec(v_idx_3450_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3457_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set_tag(v___x_3452_, 1);
lean_ctor_set(v___x_3452_, 1, v_err_3449_);
lean_ctor_set(v___x_3452_, 0, v_pos_3448_);
v___x_3457_ = v___x_3452_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_pos_3448_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_err_3449_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
lean_dec(v_err_3449_);
v___x_3459_ = lean_box(0);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v___x_3459_);
lean_ctor_set(v___x_3452_, 0, v_pos_3448_);
v___x_3461_ = v___x_3452_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_pos_3448_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_3479_, v___y_3480_);
lean_dec_ref(v_limits_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_3483_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_pos_3485_; lean_object* v_res_3486_; lean_object* v_maxChunkExtensions_3487_; lean_object* v___f_3488_; lean_object* v___x_3489_; 
v_pos_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_pos_3485_);
v_res_3486_ = lean_ctor_get(v___x_3484_, 1);
lean_inc(v_res_3486_);
lean_dec_ref_known(v___x_3484_, 2);
v_maxChunkExtensions_3487_ = lean_ctor_get(v_limits_3482_, 10);
lean_inc(v_maxChunkExtensions_3487_);
v___f_3488_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3488_, 0, v_limits_3482_);
v___x_3489_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_3488_, v_maxChunkExtensions_3487_, v_pos_3485_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_pos_3490_; lean_object* v_res_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_pos_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_pos_3490_);
v_res_3491_ = lean_ctor_get(v___x_3489_, 1);
lean_inc(v_res_3491_);
lean_dec_ref_known(v___x_3489_, 2);
v___x_3492_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3493_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3492_, v_pos_3490_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_pos_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3502_; 
v_pos_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; 
v_unused_3503_ = lean_ctor_get(v___x_3493_, 1);
lean_dec(v_unused_3503_);
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3502_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_pos_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3502_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v_res_3486_);
lean_ctor_set(v___x_3498_, 1, v_res_3491_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 1, v___x_3498_);
v___x_3500_ = v___x_3496_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_pos_3494_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
else
{
lean_object* v_pos_3504_; lean_object* v_err_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_res_3491_);
lean_dec(v_res_3486_);
v_pos_3504_ = lean_ctor_get(v___x_3493_, 0);
v_err_3505_ = lean_ctor_get(v___x_3493_, 1);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3493_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_err_3505_);
lean_inc(v_pos_3504_);
lean_dec(v___x_3493_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_pos_3504_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_err_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
else
{
lean_object* v_pos_3513_; lean_object* v_err_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec(v_res_3486_);
v_pos_3513_ = lean_ctor_get(v___x_3489_, 0);
v_err_3514_ = lean_ctor_get(v___x_3489_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3489_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_err_3514_);
lean_inc(v_pos_3513_);
lean_dec(v___x_3489_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_pos_3513_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_err_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
else
{
lean_object* v_pos_3522_; lean_object* v_err_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v_limits_3482_);
v_pos_3522_ = lean_ctor_get(v___x_3484_, 0);
v_err_3523_ = lean_ctor_get(v___x_3484_, 1);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3484_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_err_3523_);
lean_inc(v_pos_3522_);
lean_dec(v___x_3484_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_pos_3522_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_err_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object* v_x_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_obj_tag_nat(v_x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object* v_x_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(v_x_3533_);
lean_dec_ref(v_x_3533_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_3535_, lean_object* v_k_3536_){
_start:
{
if (lean_obj_tag(v_t_3535_) == 0)
{
lean_object* v_data_3537_; lean_object* v___x_3538_; 
v_data_3537_ = lean_ctor_get(v_t_3535_, 0);
lean_inc_ref(v_data_3537_);
lean_dec_ref_known(v_t_3535_, 1);
v___x_3538_ = lean_apply_1(v_k_3536_, v_data_3537_);
return v___x_3538_;
}
else
{
lean_object* v_data_3539_; lean_object* v_remaining_3540_; lean_object* v___x_3541_; 
v_data_3539_ = lean_ctor_get(v_t_3535_, 0);
lean_inc_ref(v_data_3539_);
v_remaining_3540_ = lean_ctor_get(v_t_3535_, 1);
lean_inc(v_remaining_3540_);
lean_dec_ref_known(v_t_3535_, 2);
v___x_3541_ = lean_apply_2(v_k_3536_, v_data_3539_, v_remaining_3540_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_3542_, lean_object* v_ctorIdx_3543_, lean_object* v_t_3544_, lean_object* v_h_3545_, lean_object* v_k_3546_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3544_, v_k_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_3548_, lean_object* v_ctorIdx_3549_, lean_object* v_t_3550_, lean_object* v_h_3551_, lean_object* v_k_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_3548_, v_ctorIdx_3549_, v_t_3550_, v_h_3551_, v_k_3552_);
lean_dec(v_ctorIdx_3549_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_3554_, lean_object* v_complete_3555_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3554_, v_complete_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_3557_, lean_object* v_t_3558_, lean_object* v_h_3559_, lean_object* v_complete_3560_){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3558_, v_complete_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_3562_, lean_object* v_incomplete_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3562_, v_incomplete_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_3565_, lean_object* v_t_3566_, lean_object* v_h_3567_, lean_object* v_incomplete_3568_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3566_, v_incomplete_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_3570_, v_a_3571_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_res_3573_; lean_object* v_pos_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3614_; 
v_res_3573_ = lean_ctor_get(v___x_3572_, 1);
v_pos_3574_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3576_ = v___x_3572_;
v_isShared_3577_ = v_isSharedCheck_3614_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_res_3573_);
lean_inc(v_pos_3574_);
lean_dec(v___x_3572_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3614_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_fst_3578_; lean_object* v_snd_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3613_; 
v_fst_3578_ = lean_ctor_get(v_res_3573_, 0);
v_snd_3579_ = lean_ctor_get(v_res_3573_, 1);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_res_3573_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3581_ = v_res_3573_;
v_isShared_3582_ = v_isSharedCheck_3613_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_snd_3579_);
lean_inc(v_fst_3578_);
lean_dec(v_res_3573_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3613_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_nat_dec_eq(v_fst_3578_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; 
lean_del_object(v___x_3576_);
v___x_3585_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_3578_, v_pos_3574_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_pos_3586_; lean_object* v_res_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3599_; 
v_pos_3586_ = lean_ctor_get(v___x_3585_, 0);
v_res_3587_ = lean_ctor_get(v___x_3585_, 1);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3589_ = v___x_3585_;
v_isShared_3590_ = v_isSharedCheck_3599_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_res_3587_);
lean_inc(v_pos_3586_);
lean_dec(v___x_3585_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3599_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v_res_3587_);
lean_ctor_set(v___x_3581_, 0, v_snd_3579_);
v___x_3592_ = v___x_3581_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_snd_3579_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_res_3587_);
v___x_3592_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v_fst_3578_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v___x_3594_);
v___x_3596_ = v___x_3589_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_pos_3586_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
else
{
lean_object* v_pos_3600_; lean_object* v_err_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_del_object(v___x_3581_);
lean_dec(v_snd_3579_);
lean_dec(v_fst_3578_);
v_pos_3600_ = lean_ctor_get(v___x_3585_, 0);
v_err_3601_ = lean_ctor_get(v___x_3585_, 1);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3585_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_err_3601_);
lean_inc(v_pos_3600_);
lean_dec(v___x_3585_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_pos_3600_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_err_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
lean_del_object(v___x_3581_);
lean_dec(v_snd_3579_);
lean_dec(v_fst_3578_);
v___x_3609_ = lean_box(0);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3609_);
v___x_3611_ = v___x_3576_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_pos_3574_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
else
{
lean_object* v_pos_3615_; lean_object* v_err_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
v_pos_3615_ = lean_ctor_get(v___x_3572_, 0);
v_err_3616_ = lean_ctor_get(v___x_3572_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3572_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_err_3616_);
lean_inc(v_pos_3615_);
lean_dec(v___x_3572_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_pos_3615_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_err_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_3624_, lean_object* v_it_3625_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3626_ = l_ByteArray_Iterator_remainingBytes(v_it_3625_);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = lean_nat_dec_eq(v___x_3626_, v___x_3627_);
if (v___x_3628_ == 0)
{
uint8_t v___x_3629_; 
v___x_3629_ = lean_nat_dec_lt(v___x_3626_, v_size_3624_);
if (v___x_3629_ == 0)
{
lean_object* v_array_3630_; lean_object* v_idx_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3650_; 
lean_dec(v___x_3626_);
v_array_3630_ = lean_ctor_get(v_it_3625_, 0);
v_idx_3631_ = lean_ctor_get(v_it_3625_, 1);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_it_3625_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3633_ = v_it_3625_;
v_isShared_3634_ = v_isSharedCheck_3650_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_idx_3631_);
lean_inc(v_array_3630_);
lean_dec(v_it_3625_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3650_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3635_ = lean_nat_add(v_idx_3631_, v_size_3624_);
lean_inc(v___x_3635_);
lean_inc_ref(v_array_3630_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 1, v___x_3635_);
v___x_3637_ = v___x_3633_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_array_3630_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v_lower_3639_; lean_object* v_upper_3640_; lean_object* v___x_3644_; lean_object* v___y_3646_; uint8_t v___x_3648_; 
v___x_3644_ = lean_byte_array_size(v_array_3630_);
v___x_3648_ = lean_nat_dec_le(v_idx_3631_, v___x_3627_);
if (v___x_3648_ == 0)
{
v___y_3646_ = v_idx_3631_;
goto v___jp_3645_;
}
else
{
lean_dec(v_idx_3631_);
v___y_3646_ = v___x_3627_;
goto v___jp_3645_;
}
v___jp_3638_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = l_ByteArray_toByteSlice(v_array_3630_, v_lower_3639_, v_upper_3640_);
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3637_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
return v___x_3643_;
}
v___jp_3645_:
{
uint8_t v___x_3647_; 
v___x_3647_ = lean_nat_dec_le(v___x_3635_, v___x_3644_);
if (v___x_3647_ == 0)
{
lean_dec(v___x_3635_);
v_lower_3639_ = v___y_3646_;
v_upper_3640_ = v___x_3644_;
goto v___jp_3638_;
}
else
{
v_lower_3639_ = v___y_3646_;
v_upper_3640_ = v___x_3635_;
goto v___jp_3638_;
}
}
}
}
}
else
{
lean_object* v_array_3651_; lean_object* v_idx_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3672_; 
v_array_3651_ = lean_ctor_get(v_it_3625_, 0);
v_idx_3652_ = lean_ctor_get(v_it_3625_, 1);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_it_3625_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3654_ = v_it_3625_;
v_isShared_3655_ = v_isSharedCheck_3672_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_idx_3652_);
lean_inc(v_array_3651_);
lean_dec(v_it_3625_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3672_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3656_ = lean_nat_add(v_idx_3652_, v___x_3626_);
lean_inc(v___x_3656_);
lean_inc_ref(v_array_3651_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 1, v___x_3656_);
v___x_3658_ = v___x_3654_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_array_3651_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v_lower_3660_; lean_object* v_upper_3661_; lean_object* v___x_3666_; lean_object* v___y_3668_; uint8_t v___x_3670_; 
v___x_3666_ = lean_byte_array_size(v_array_3651_);
v___x_3670_ = lean_nat_dec_le(v_idx_3652_, v___x_3627_);
if (v___x_3670_ == 0)
{
v___y_3668_ = v_idx_3652_;
goto v___jp_3667_;
}
else
{
lean_dec(v_idx_3652_);
v___y_3668_ = v___x_3627_;
goto v___jp_3667_;
}
v___jp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3662_ = l_ByteArray_toByteSlice(v_array_3651_, v_lower_3660_, v_upper_3661_);
v___x_3663_ = lean_nat_sub(v_size_3624_, v___x_3626_);
lean_dec(v___x_3626_);
v___x_3664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3658_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
return v___x_3665_;
}
v___jp_3667_:
{
uint8_t v___x_3669_; 
v___x_3669_ = lean_nat_dec_le(v___x_3656_, v___x_3666_);
if (v___x_3669_ == 0)
{
lean_dec(v___x_3656_);
v_lower_3660_ = v___y_3668_;
v_upper_3661_ = v___x_3666_;
goto v___jp_3659_;
}
else
{
v_lower_3660_ = v___y_3668_;
v_upper_3661_ = v___x_3656_;
goto v___jp_3659_;
}
}
}
}
}
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
lean_dec(v___x_3626_);
v___x_3673_ = lean_box(0);
v___x_3674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3674_, 0, v_it_3625_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3675_, lean_object* v_it_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3675_, v_it_3676_);
lean_dec(v_size_3675_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_res_3681_; 
v_res_3681_ = lean_ctor_get(v___x_3680_, 1);
if (lean_obj_tag(v_res_3681_) == 0)
{
lean_object* v_pos_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_inc_ref(v_res_3681_);
v_pos_3682_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_pos_3682_);
lean_dec_ref_known(v___x_3680_, 2);
v___x_3683_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3684_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3683_, v_pos_3682_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_pos_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
v_pos_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; 
v_unused_3693_ = lean_ctor_get(v___x_3684_, 1);
lean_dec(v_unused_3693_);
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_pos_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 1, v_res_3681_);
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_pos_3685_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_res_3681_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
else
{
lean_object* v_pos_3694_; lean_object* v_err_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec_ref_known(v_res_3681_, 1);
v_pos_3694_ = lean_ctor_get(v___x_3684_, 0);
v_err_3695_ = lean_ctor_get(v___x_3684_, 1);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3684_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_err_3695_);
lean_inc(v_pos_3694_);
lean_dec(v___x_3684_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_pos_3694_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_err_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
return v___x_3680_;
}
}
else
{
return v___x_3680_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3703_, v_a_3704_);
lean_dec(v_size_3703_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object* v_s_3706_, lean_object* v_p_3707_){
_start:
{
uint32_t v___y_3709_; lean_object* v___x_3714_; uint8_t v_decide_3715_; 
v___x_3714_ = lean_string_utf8_byte_size(v_s_3706_);
v_decide_3715_ = lean_nat_dec_eq(v_p_3707_, v___x_3714_);
if (v_decide_3715_ == 0)
{
uint32_t v___x_3716_; uint32_t v___x_3717_; uint8_t v___x_3718_; 
v___x_3716_ = lean_string_utf8_get_fast(v_s_3706_, v_p_3707_);
v___x_3717_ = 65;
v___x_3718_ = lean_uint32_dec_le(v___x_3717_, v___x_3716_);
if (v___x_3718_ == 0)
{
v___y_3709_ = v___x_3716_;
goto v___jp_3708_;
}
else
{
uint32_t v___x_3719_; uint8_t v___x_3720_; 
v___x_3719_ = 90;
v___x_3720_ = lean_uint32_dec_le(v___x_3716_, v___x_3719_);
if (v___x_3720_ == 0)
{
v___y_3709_ = v___x_3716_;
goto v___jp_3708_;
}
else
{
uint32_t v___x_3721_; uint32_t v___x_3722_; 
v___x_3721_ = 32;
v___x_3722_ = lean_uint32_add(v___x_3716_, v___x_3721_);
v___y_3709_ = v___x_3722_;
goto v___jp_3708_;
}
}
}
else
{
lean_dec(v_p_3707_);
return v_s_3706_;
}
v___jp_3708_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_inc(v_p_3707_);
v___x_3710_ = lean_string_utf8_set(v_s_3706_, v_p_3707_, v___y_3709_);
v___x_3711_ = l_Char_utf8Size(v___y_3709_);
v___x_3712_ = lean_nat_add(v_p_3707_, v___x_3711_);
lean_dec(v___x_3711_);
lean_dec(v_p_3707_);
v_s_3706_ = v___x_3710_;
v_p_3707_ = v___x_3712_;
goto _start;
}
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3735_){
_start:
{
lean_object* v___x_3736_; lean_object* v_n_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v___x_3736_ = lean_unsigned_to_nat(0u);
v_n_3737_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(v_name_3735_, v___x_3736_);
v___x_3738_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3739_ = lean_string_dec_eq(v_n_3737_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; uint8_t v___x_3741_; 
v___x_3740_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3741_ = lean_string_dec_eq(v_n_3737_, v___x_3740_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; uint8_t v___x_3743_; 
v___x_3742_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3743_ = lean_string_dec_eq(v_n_3737_, v___x_3742_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3744_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3745_ = lean_string_dec_eq(v_n_3737_, v___x_3744_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; uint8_t v___x_3747_; 
v___x_3746_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3747_ = lean_string_dec_eq(v_n_3737_, v___x_3746_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___x_3748_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5));
v___x_3749_ = lean_string_dec_eq(v_n_3737_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3750_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6));
v___x_3751_ = lean_string_dec_eq(v_n_3737_, v___x_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; uint8_t v___x_3753_; 
v___x_3752_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7));
v___x_3753_ = lean_string_dec_eq(v_n_3737_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8));
v___x_3755_ = lean_string_dec_eq(v_n_3737_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3756_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9));
v___x_3757_ = lean_string_dec_eq(v_n_3737_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3758_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10));
v___x_3759_ = lean_string_dec_eq(v_n_3737_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11));
v___x_3761_ = lean_string_dec_eq(v_n_3737_, v___x_3760_);
lean_dec_ref(v_n_3737_);
return v___x_3761_;
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3759_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3757_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3755_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3753_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3751_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3749_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3747_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3745_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3743_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3741_;
}
}
else
{
lean_dec_ref(v_n_3737_);
return v___x_3739_;
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3735_ = stack[0].m_obj;
uint8_t v_res_3762_;
v_res_3762_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3735_);
stack->m_num = v_res_3762_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3763_){
_start:
{
uint8_t v_res_3764_; lean_object* v_r_3765_; 
v_res_3764_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3763_);
v_r_3765_ = lean_box(v_res_3764_);
return v_r_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3767_, v_a_3768_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_res_3770_; 
v_res_3770_ = lean_ctor_get(v___x_3769_, 1);
lean_inc(v_res_3770_);
if (lean_obj_tag(v_res_3770_) == 1)
{
lean_object* v_val_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3792_; 
v_val_3771_ = lean_ctor_get(v_res_3770_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_res_3770_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3773_ = v_res_3770_;
v_isShared_3774_ = v_isSharedCheck_3792_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_val_3771_);
lean_dec(v_res_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3792_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v_pos_3775_; lean_object* v_fst_3776_; uint8_t v___x_3777_; 
v_pos_3775_ = lean_ctor_get(v___x_3769_, 0);
v_fst_3776_ = lean_ctor_get(v_val_3771_, 0);
lean_inc_n(v_fst_3776_, 2);
lean_dec(v_val_3771_);
v___x_3777_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3776_);
if (v___x_3777_ == 0)
{
lean_dec(v_fst_3776_);
lean_del_object(v___x_3773_);
return v___x_3769_;
}
else
{
lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3789_; 
lean_inc(v_pos_3775_);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3789_ == 0)
{
lean_object* v_unused_3790_; lean_object* v_unused_3791_; 
v_unused_3790_ = lean_ctor_get(v___x_3769_, 1);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v___x_3769_, 0);
lean_dec(v_unused_3791_);
v___x_3779_ = v___x_3769_;
v_isShared_3780_ = v_isSharedCheck_3789_;
goto v_resetjp_3778_;
}
else
{
lean_dec(v___x_3769_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3789_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3784_; 
v___x_3781_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3782_ = lean_string_append(v___x_3781_, v_fst_3776_);
lean_dec(v_fst_3776_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 0, v___x_3782_);
v___x_3784_ = v___x_3773_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3786_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set_tag(v___x_3779_, 1);
lean_ctor_set(v___x_3779_, 1, v___x_3784_);
v___x_3786_ = v___x_3779_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_pos_3775_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3770_);
return v___x_3769_;
}
}
else
{
return v___x_3769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3793_, lean_object* v_a_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3793_, v_a_3794_);
lean_dec_ref(v_limits_3793_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_maxTrailerHeaders_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_maxTrailerHeaders_3798_ = lean_ctor_get(v_limits_3796_, 17);
lean_inc(v_maxTrailerHeaders_3798_);
v___x_3799_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3799_, 0, v_limits_3796_);
v___x_3800_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3799_, v_maxTrailerHeaders_3798_, v_a_3797_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_pos_3801_; lean_object* v_res_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_pos_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_pos_3801_);
v_res_3802_ = lean_ctor_get(v___x_3800_, 1);
lean_inc(v_res_3802_);
lean_dec_ref_known(v___x_3800_, 2);
v___x_3803_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3804_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3803_, v_pos_3801_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_pos_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
v_pos_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; 
v_unused_3813_ = lean_ctor_get(v___x_3804_, 1);
lean_dec(v_unused_3813_);
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_pos_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 1, v_res_3802_);
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_pos_3805_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_res_3802_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
else
{
lean_object* v_pos_3814_; lean_object* v_err_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec(v_res_3802_);
v_pos_3814_ = lean_ctor_get(v___x_3804_, 0);
v_err_3815_ = lean_ctor_get(v___x_3804_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3804_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_err_3815_);
lean_inc(v_pos_3814_);
lean_dec(v___x_3804_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_pos_3814_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_err_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
return v___x_3800_;
}
}
}
uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3823_){
_start:
{
uint32_t v___x_3824_; uint32_t v___x_3830_; uint8_t v___x_3831_; 
v___x_3824_ = lean_uint8_to_uint32(v_c_3823_);
v___x_3830_ = 33;
v___x_3831_ = lean_uint32_dec_le(v___x_3830_, v___x_3824_);
if (v___x_3831_ == 0)
{
goto v___jp_3825_;
}
else
{
uint32_t v___x_3832_; uint8_t v___x_3833_; 
v___x_3832_ = 126;
v___x_3833_ = lean_uint32_dec_le(v___x_3824_, v___x_3832_);
if (v___x_3833_ == 0)
{
goto v___jp_3825_;
}
else
{
return v___x_3833_;
}
}
v___jp_3825_:
{
uint32_t v___x_3826_; uint8_t v___x_3827_; 
v___x_3826_ = 32;
v___x_3827_ = lean_uint32_dec_eq(v___x_3824_, v___x_3826_);
if (v___x_3827_ == 0)
{
uint32_t v___x_3828_; uint8_t v___x_3829_; 
v___x_3828_ = 9;
v___x_3829_ = lean_uint32_dec_eq(v___x_3824_, v___x_3828_);
return v___x_3829_;
}
else
{
return v___x_3827_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_3823_ = stack[0].m_num;
uint8_t v_res_3834_;
v_res_3834_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_3823_);
stack->m_num = v_res_3834_;
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3835_){
_start:
{
uint8_t v_c_boxed_3836_; uint8_t v_res_3837_; lean_object* v_r_3838_; 
v_c_boxed_3836_ = lean_unbox(v_c_3835_);
v_res_3837_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3836_);
v_r_3838_ = lean_box(v_res_3837_);
return v_r_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v_maxReasonPhraseLength_3841_; lean_object* v___f_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v_snd_3845_; lean_object* v_snd_3846_; uint8_t v___x_3847_; 
v_maxReasonPhraseLength_3841_ = lean_ctor_get(v_limits_3839_, 16);
v___f_3842_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_3843_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3840_);
v___x_3844_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3842_, v_maxReasonPhraseLength_3841_, v___x_3843_, v_a_3840_);
v_snd_3845_ = lean_ctor_get(v___x_3844_, 1);
lean_inc(v_snd_3845_);
v_snd_3846_ = lean_ctor_get(v_snd_3845_, 1);
v___x_3847_ = lean_unbox(v_snd_3846_);
if (v___x_3847_ == 0)
{
lean_object* v_fst_3848_; lean_object* v_fst_3849_; lean_object* v_array_3850_; lean_object* v_idx_3851_; lean_object* v_lower_3853_; lean_object* v_upper_3854_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___y_3866_; uint8_t v___x_3868_; 
v_fst_3848_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_fst_3848_);
lean_dec_ref(v___x_3844_);
v_fst_3849_ = lean_ctor_get(v_snd_3845_, 0);
lean_inc(v_fst_3849_);
lean_dec(v_snd_3845_);
v_array_3850_ = lean_ctor_get(v_a_3840_, 0);
lean_inc_ref(v_array_3850_);
v_idx_3851_ = lean_ctor_get(v_a_3840_, 1);
lean_inc(v_idx_3851_);
lean_dec_ref(v_a_3840_);
v___x_3863_ = lean_nat_add(v_idx_3851_, v_fst_3848_);
lean_dec(v_fst_3848_);
v___x_3864_ = lean_byte_array_size(v_array_3850_);
v___x_3868_ = lean_nat_dec_le(v_idx_3851_, v___x_3843_);
if (v___x_3868_ == 0)
{
v___y_3866_ = v_idx_3851_;
goto v___jp_3865_;
}
else
{
lean_dec(v_idx_3851_);
v___y_3866_ = v___x_3843_;
goto v___jp_3865_;
}
v___jp_3852_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v___x_3855_ = l_ByteArray_toByteSlice(v_array_3850_, v_lower_3853_, v_upper_3854_);
v___x_3856_ = l_ByteSlice_toByteArray(v___x_3855_);
v___x_3857_ = lean_string_validate_utf8(v___x_3856_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec_ref(v___x_3856_);
v___x_3858_ = lean_box(0);
v___x_3859_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3858_, v_fst_3849_);
return v___x_3859_;
}
else
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3860_ = lean_string_from_utf8_unchecked(v___x_3856_);
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
v___x_3862_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3861_, v_fst_3849_);
lean_dec_ref_known(v___x_3861_, 1);
return v___x_3862_;
}
}
v___jp_3865_:
{
uint8_t v___x_3867_; 
v___x_3867_ = lean_nat_dec_le(v___x_3863_, v___x_3864_);
if (v___x_3867_ == 0)
{
lean_dec(v___x_3863_);
v_lower_3853_ = v___y_3866_;
v_upper_3854_ = v___x_3864_;
goto v___jp_3852_;
}
else
{
v_lower_3853_ = v___y_3866_;
v_upper_3854_ = v___x_3863_;
goto v___jp_3852_;
}
}
}
else
{
lean_object* v_fst_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3877_; 
lean_dec_ref(v___x_3844_);
lean_dec_ref(v_a_3840_);
v_fst_3869_ = lean_ctor_get(v_snd_3845_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_snd_3845_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; 
v_unused_3878_ = lean_ctor_get(v_snd_3845_, 1);
lean_dec(v_unused_3878_);
v___x_3871_ = v_snd_3845_;
v_isShared_3872_ = v_isSharedCheck_3877_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_fst_3869_);
lean_dec(v_snd_3845_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3877_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3873_ = lean_box(0);
if (v_isShared_3872_ == 0)
{
lean_ctor_set_tag(v___x_3871_, 1);
lean_ctor_set(v___x_3871_, 1, v___x_3873_);
v___x_3875_ = v___x_3871_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_fst_3869_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3879_, v_a_3880_);
lean_dec_ref(v_limits_3879_);
return v_res_3881_;
}
}
uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3882_){
_start:
{
if (lean_obj_tag(v_x_3882_) == 0)
{
uint8_t v___x_3883_; 
v___x_3883_ = 1;
return v___x_3883_;
}
else
{
lean_object* v_head_3884_; lean_object* v_tail_3885_; uint32_t v___x_3886_; uint32_t v___x_3887_; uint8_t v___x_3888_; 
v_head_3884_ = lean_ctor_get(v_x_3882_, 0);
v_tail_3885_ = lean_ctor_get(v_x_3882_, 1);
v___x_3886_ = 9;
v___x_3887_ = lean_unbox_uint32(v_head_3884_);
v___x_3888_ = lean_uint32_dec_eq(v___x_3887_, v___x_3886_);
if (v___x_3888_ == 0)
{
uint32_t v___x_3889_; uint32_t v___x_3890_; uint8_t v___x_3891_; 
v___x_3889_ = 32;
v___x_3890_ = lean_unbox_uint32(v_head_3884_);
v___x_3891_ = lean_uint32_dec_eq(v___x_3890_, v___x_3889_);
if (v___x_3891_ == 0)
{
uint32_t v___x_3892_; uint32_t v___x_3893_; uint8_t v___x_3894_; 
v___x_3892_ = 33;
v___x_3893_ = lean_unbox_uint32(v_head_3884_);
v___x_3894_ = lean_uint32_dec_le(v___x_3892_, v___x_3893_);
if (v___x_3894_ == 0)
{
return v___x_3894_;
}
else
{
uint32_t v___x_3895_; uint32_t v___x_3896_; uint8_t v___x_3897_; 
v___x_3895_ = 126;
v___x_3896_ = lean_unbox_uint32(v_head_3884_);
v___x_3897_ = lean_uint32_dec_le(v___x_3896_, v___x_3895_);
if (v___x_3897_ == 0)
{
return v___x_3897_;
}
else
{
v_x_3882_ = v_tail_3885_;
goto _start;
}
}
}
else
{
v_x_3882_ = v_tail_3885_;
goto _start;
}
}
else
{
v_x_3882_ = v_tail_3885_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3882_ = stack[0].m_obj;
uint8_t v_res_3901_;
v_res_3901_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3882_);
stack->m_num = v_res_3901_;
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3902_){
_start:
{
uint8_t v_res_3903_; lean_object* v_r_3904_; 
v_res_3903_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3902_);
lean_dec(v_x_3902_);
v_r_3904_ = lean_box(v_res_3903_);
return v_r_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v___y_3911_; lean_object* v_array_3917_; lean_object* v_idx_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_array_3917_ = lean_ctor_get(v_a_3909_, 0);
v_idx_3918_ = lean_ctor_get(v_a_3909_, 1);
v___x_3919_ = lean_byte_array_size(v_array_3917_);
v___x_3920_ = lean_nat_dec_lt(v_idx_3918_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_box(0);
v___x_3922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3922_, 0, v_a_3909_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
return v___x_3922_;
}
else
{
uint8_t v_c_3923_; uint8_t v___x_3924_; uint8_t v___x_3925_; 
v_c_3923_ = lean_byte_array_fget(v_array_3917_, v_idx_3918_);
v___x_3924_ = 48;
v___x_3925_ = lean_uint8_dec_le(v___x_3924_, v_c_3923_);
if (v___x_3925_ == 0)
{
goto v___jp_3914_;
}
else
{
uint8_t v___x_3926_; uint8_t v___x_3927_; 
v___x_3926_ = 57;
v___x_3927_ = lean_uint8_dec_le(v_c_3923_, v___x_3926_);
if (v___x_3927_ == 0)
{
goto v___jp_3914_;
}
else
{
lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_4020_; 
lean_inc(v_idx_3918_);
lean_inc_ref(v_array_3917_);
v_isSharedCheck_4020_ = !lean_is_exclusive(v_a_3909_);
if (v_isSharedCheck_4020_ == 0)
{
lean_object* v_unused_4021_; lean_object* v_unused_4022_; 
v_unused_4021_ = lean_ctor_get(v_a_3909_, 1);
lean_dec(v_unused_4021_);
v_unused_4022_ = lean_ctor_get(v_a_3909_, 0);
lean_dec(v_unused_4022_);
v___x_3929_ = v_a_3909_;
v_isShared_3930_ = v_isSharedCheck_4020_;
goto v_resetjp_3928_;
}
else
{
lean_dec(v_a_3909_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_4020_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v_it_x27_3934_; 
v___x_3931_ = lean_unsigned_to_nat(1u);
v___x_3932_ = lean_nat_add(v_idx_3918_, v___x_3931_);
lean_dec(v_idx_3918_);
lean_inc(v___x_3932_);
lean_inc_ref(v_array_3917_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 1, v___x_3932_);
v_it_x27_3934_ = v___x_3929_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_array_3917_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v___x_3932_);
v_it_x27_3934_ = v_reuseFailAlloc_4019_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
uint8_t v___x_3938_; 
v___x_3938_ = lean_nat_dec_lt(v___x_3932_, v___x_3919_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec(v___x_3932_);
lean_dec_ref(v_array_3917_);
v___x_3939_ = lean_box(0);
v___x_3940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3940_, 0, v_it_x27_3934_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
return v___x_3940_;
}
else
{
uint8_t v_c_3941_; uint8_t v___x_3942_; 
v_c_3941_ = lean_byte_array_fget(v_array_3917_, v___x_3932_);
v___x_3942_ = lean_uint8_dec_le(v___x_3924_, v_c_3941_);
if (v___x_3942_ == 0)
{
lean_dec(v___x_3932_);
lean_dec_ref(v_array_3917_);
goto v___jp_3935_;
}
else
{
uint8_t v___x_3943_; 
v___x_3943_ = lean_uint8_dec_le(v_c_3941_, v___x_3926_);
if (v___x_3943_ == 0)
{
lean_dec(v___x_3932_);
lean_dec_ref(v_array_3917_);
goto v___jp_3935_;
}
else
{
lean_object* v___x_3944_; lean_object* v_it_x27_3945_; uint8_t v___x_3949_; 
lean_dec_ref(v_it_x27_3934_);
v___x_3944_ = lean_nat_add(v___x_3932_, v___x_3931_);
lean_dec(v___x_3932_);
lean_inc(v___x_3944_);
lean_inc_ref(v_array_3917_);
v_it_x27_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3945_, 0, v_array_3917_);
lean_ctor_set(v_it_x27_3945_, 1, v___x_3944_);
v___x_3949_ = lean_nat_dec_lt(v___x_3944_, v___x_3919_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec(v___x_3944_);
lean_dec_ref(v_array_3917_);
v___x_3950_ = lean_box(0);
v___x_3951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3951_, 0, v_it_x27_3945_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
return v___x_3951_;
}
else
{
uint8_t v_c_3952_; uint8_t v___x_3953_; 
v_c_3952_ = lean_byte_array_fget(v_array_3917_, v___x_3944_);
v___x_3953_ = lean_uint8_dec_le(v___x_3924_, v_c_3952_);
if (v___x_3953_ == 0)
{
lean_dec(v___x_3944_);
lean_dec_ref(v_array_3917_);
goto v___jp_3946_;
}
else
{
uint8_t v___x_3954_; 
v___x_3954_ = lean_uint8_dec_le(v_c_3952_, v___x_3926_);
if (v___x_3954_ == 0)
{
lean_dec(v___x_3944_);
lean_dec_ref(v_array_3917_);
goto v___jp_3946_;
}
else
{
lean_object* v___x_3955_; lean_object* v_it_x27_3956_; uint8_t v___x_3957_; 
lean_dec_ref_known(v_it_x27_3945_, 2);
v___x_3955_ = lean_nat_add(v___x_3944_, v___x_3931_);
lean_dec(v___x_3944_);
lean_inc(v___x_3955_);
lean_inc_ref(v_array_3917_);
v_it_x27_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3956_, 0, v_array_3917_);
lean_ctor_set(v_it_x27_3956_, 1, v___x_3955_);
v___x_3957_ = lean_nat_dec_lt(v___x_3955_, v___x_3919_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_dec(v___x_3955_);
lean_dec_ref(v_array_3917_);
v___x_3958_ = lean_box(0);
v___x_3959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3959_, 0, v_it_x27_3956_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
return v___x_3959_;
}
else
{
uint8_t v___x_3960_; uint8_t v_got_3961_; uint8_t v___x_3962_; 
v___x_3960_ = 32;
v_got_3961_ = lean_byte_array_fget(v_array_3917_, v___x_3955_);
v___x_3962_ = lean_uint8_dec_eq(v_got_3961_, v___x_3960_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_dec(v___x_3955_);
lean_dec_ref(v_array_3917_);
v___x_3963_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3964_, 0, v_it_x27_3956_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
return v___x_3964_;
}
else
{
lean_object* v___x_3965_; uint32_t v___x_3966_; uint32_t v___x_3967_; uint32_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v_pos_3982_; lean_object* v_res_3983_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
lean_dec_ref_known(v_it_x27_3956_, 2);
v___x_3965_ = lean_unsigned_to_nat(48u);
v___x_3966_ = lean_uint8_to_uint32(v_c_3923_);
v___x_3967_ = lean_uint8_to_uint32(v_c_3941_);
v___x_3968_ = lean_uint8_to_uint32(v_c_3952_);
v___x_3969_ = lean_uint32_to_nat(v___x_3966_);
v___x_3970_ = lean_nat_sub(v___x_3969_, v___x_3965_);
lean_dec(v___x_3969_);
v___x_3971_ = lean_unsigned_to_nat(100u);
v___x_3972_ = lean_nat_mul(v___x_3970_, v___x_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_uint32_to_nat(v___x_3967_);
v___x_3974_ = lean_nat_sub(v___x_3973_, v___x_3965_);
lean_dec(v___x_3973_);
v___x_3975_ = lean_unsigned_to_nat(10u);
v___x_3976_ = lean_nat_mul(v___x_3974_, v___x_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_nat_add(v___x_3972_, v___x_3976_);
lean_dec(v___x_3976_);
lean_dec(v___x_3972_);
v___x_3978_ = lean_uint32_to_nat(v___x_3968_);
v___x_3979_ = lean_nat_sub(v___x_3978_, v___x_3965_);
lean_dec(v___x_3978_);
v___x_3980_ = lean_nat_add(v___x_3977_, v___x_3979_);
lean_dec(v___x_3979_);
lean_dec(v___x_3977_);
v___x_3991_ = lean_nat_add(v___x_3955_, v___x_3931_);
lean_dec(v___x_3955_);
v___x_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3992_, 0, v_array_3917_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3908_, v___x_3992_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_pos_3994_; lean_object* v_res_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v_pos_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_pos_3994_);
v_res_3995_ = lean_ctor_get(v___x_3993_, 1);
lean_inc(v_res_3995_);
lean_dec_ref_known(v___x_3993_, 2);
v___x_3996_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3997_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3996_, v_pos_3994_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_pos_3998_; 
v_pos_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_pos_3998_);
lean_dec_ref_known(v___x_3997_, 2);
v_pos_3982_ = v_pos_3998_;
v_res_3983_ = v_res_3995_;
goto v___jp_3981_;
}
else
{
lean_object* v_pos_3999_; lean_object* v_err_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v_res_3995_);
lean_dec(v___x_3980_);
v_pos_3999_ = lean_ctor_get(v___x_3997_, 0);
v_err_4000_ = lean_ctor_get(v___x_3997_, 1);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3997_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_err_4000_);
lean_inc(v_pos_3999_);
lean_dec(v___x_3997_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_pos_3999_);
lean_ctor_set(v_reuseFailAlloc_4006_, 1, v_err_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_pos_4008_; lean_object* v_res_4009_; 
v_pos_4008_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_pos_4008_);
v_res_4009_ = lean_ctor_get(v___x_3993_, 1);
lean_inc(v_res_4009_);
lean_dec_ref_known(v___x_3993_, 2);
v_pos_3982_ = v_pos_4008_;
v_res_3983_ = v_res_4009_;
goto v___jp_3981_;
}
else
{
lean_object* v_pos_4010_; lean_object* v_err_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v___x_3980_);
v_pos_4010_ = lean_ctor_get(v___x_3993_, 0);
v_err_4011_ = lean_ctor_get(v___x_3993_, 1);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3993_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_err_4011_);
lean_inc(v_pos_4010_);
lean_dec(v___x_3993_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_pos_4010_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_err_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
v___jp_3981_:
{
lean_object* v___x_3984_; uint8_t v___x_3985_; 
lean_inc_ref(v_res_3983_);
v___x_3984_ = l_String_toListImpl(v_res_3983_);
v___x_3985_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3984_);
lean_dec(v___x_3984_);
if (v___x_3985_ == 0)
{
lean_dec_ref(v_res_3983_);
lean_dec(v___x_3980_);
v___y_3911_ = v_pos_3982_;
goto v___jp_3910_;
}
else
{
lean_object* v___x_3986_; uint16_t v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3986_, 0, v_res_3983_);
v___x_3987_ = lean_uint16_of_nat(v___x_3980_);
lean_dec(v___x_3980_);
v___x_3988_ = l_Std_Http_Status_ofCode(v___x_3986_, v___x_3987_);
if (lean_obj_tag(v___x_3988_) == 1)
{
lean_object* v_val_3989_; lean_object* v___x_3990_; 
v_val_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_val_3989_);
lean_dec_ref_known(v___x_3988_, 1);
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v_pos_3982_);
lean_ctor_set(v___x_3990_, 1, v_val_3989_);
return v___x_3990_;
}
else
{
lean_dec(v___x_3988_);
v___y_3911_ = v_pos_3982_;
goto v___jp_3910_;
}
}
}
}
}
}
}
}
v___jp_3946_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3948_, 0, v_it_x27_3945_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
return v___x_3948_;
}
}
}
}
v___jp_3935_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3937_, 0, v_it_x27_3934_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
return v___x_3937_;
}
}
}
}
}
}
v___jp_3910_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_3913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___y_3911_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
return v___x_3913_;
}
v___jp_3914_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3916_, 0, v_a_3909_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
return v___x_3916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4023_, v_a_4024_);
lean_dec_ref(v_limits_4023_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_4026_, lean_object* v_a_4027_){
_start:
{
lean_object* v___y_4029_; lean_object* v___y_4033_; uint8_t v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v_pos_4044_; lean_object* v_res_4045_; lean_object* v___x_4073_; 
v___x_4073_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4027_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_pos_4074_; lean_object* v_res_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4105_; 
v_pos_4074_ = lean_ctor_get(v___x_4073_, 0);
v_res_4075_ = lean_ctor_get(v___x_4073_, 1);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4077_ = v___x_4073_;
v_isShared_4078_ = v_isSharedCheck_4105_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_res_4075_);
lean_inc(v_pos_4074_);
lean_dec(v___x_4073_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4105_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v_array_4079_; lean_object* v_idx_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v_array_4079_ = lean_ctor_get(v_pos_4074_, 0);
v_idx_4080_ = lean_ctor_get(v_pos_4074_, 1);
v___x_4081_ = lean_byte_array_size(v_array_4079_);
v___x_4082_ = lean_nat_dec_lt(v_idx_4080_, v___x_4081_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; lean_object* v___x_4085_; 
lean_dec(v_res_4075_);
v___x_4083_ = lean_box(0);
if (v_isShared_4078_ == 0)
{
lean_ctor_set_tag(v___x_4077_, 1);
lean_ctor_set(v___x_4077_, 1, v___x_4083_);
v___x_4085_ = v___x_4077_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_pos_4074_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4083_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
else
{
uint8_t v___x_4087_; uint8_t v_got_4088_; uint8_t v___x_4089_; 
v___x_4087_ = 32;
v_got_4088_ = lean_byte_array_fget(v_array_4079_, v_idx_4080_);
v___x_4089_ = lean_uint8_dec_eq(v_got_4088_, v___x_4087_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4092_; 
lean_dec(v_res_4075_);
v___x_4090_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_4078_ == 0)
{
lean_ctor_set_tag(v___x_4077_, 1);
lean_ctor_set(v___x_4077_, 1, v___x_4090_);
v___x_4092_ = v___x_4077_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_pos_4074_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4090_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
else
{
lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4102_; 
lean_inc(v_idx_4080_);
lean_inc_ref(v_array_4079_);
lean_del_object(v___x_4077_);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_pos_4074_);
if (v_isSharedCheck_4102_ == 0)
{
lean_object* v_unused_4103_; lean_object* v_unused_4104_; 
v_unused_4103_ = lean_ctor_get(v_pos_4074_, 1);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_pos_4074_, 0);
lean_dec(v_unused_4104_);
v___x_4095_ = v_pos_4074_;
v_isShared_4096_ = v_isSharedCheck_4102_;
goto v_resetjp_4094_;
}
else
{
lean_dec(v_pos_4074_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4102_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4100_; 
v___x_4097_ = lean_unsigned_to_nat(1u);
v___x_4098_ = lean_nat_add(v_idx_4080_, v___x_4097_);
lean_dec(v_idx_4080_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 1, v___x_4098_);
v___x_4100_ = v___x_4095_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_array_4079_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
v_pos_4044_ = v___x_4100_;
v_res_4045_ = v_res_4075_;
goto v___jp_4043_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_pos_4106_; lean_object* v_res_4107_; 
v_pos_4106_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_pos_4106_);
v_res_4107_ = lean_ctor_get(v___x_4073_, 1);
lean_inc(v_res_4107_);
lean_dec_ref_known(v___x_4073_, 2);
v_pos_4044_ = v_pos_4106_;
v_res_4045_ = v_res_4107_;
goto v___jp_4043_;
}
else
{
lean_object* v_pos_4108_; lean_object* v_err_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
v_pos_4108_ = lean_ctor_get(v___x_4073_, 0);
v_err_4109_ = lean_ctor_get(v___x_4073_, 1);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4073_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_err_4109_);
lean_inc(v_pos_4108_);
lean_dec(v___x_4073_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_pos_4108_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_err_4109_);
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
v___jp_4028_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___y_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
return v___x_4031_;
}
v___jp_4032_:
{
if (v___y_4034_ == 0)
{
lean_dec(v___y_4036_);
lean_dec(v___y_4033_);
v___y_4029_ = v___y_4035_;
goto v___jp_4028_;
}
else
{
lean_object* v___x_4037_; uint8_t v___x_4038_; 
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = lean_nat_dec_eq(v___y_4036_, v___x_4037_);
lean_dec(v___y_4036_);
if (v___x_4038_ == 0)
{
lean_dec(v___y_4033_);
v___y_4029_ = v___y_4035_;
goto v___jp_4028_;
}
else
{
uint8_t v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4039_ = 0;
v___x_4040_ = l_Std_Http_Headers_empty;
v___x_4041_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4041_, 0, v___y_4033_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
lean_ctor_set_uint8(v___x_4041_, sizeof(void*)*2, v___x_4039_);
v___x_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___y_4035_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
return v___x_4042_;
}
}
}
v___jp_4043_:
{
lean_object* v_fst_4046_; lean_object* v_snd_4047_; lean_object* v___x_4048_; 
v_fst_4046_ = lean_ctor_get(v_res_4045_, 0);
lean_inc(v_fst_4046_);
v_snd_4047_ = lean_ctor_get(v_res_4045_, 1);
lean_inc(v_snd_4047_);
lean_dec_ref(v_res_4045_);
v___x_4048_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4026_, v_pos_4044_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_pos_4049_; lean_object* v_res_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4063_; 
v_pos_4049_ = lean_ctor_get(v___x_4048_, 0);
v_res_4050_ = lean_ctor_get(v___x_4048_, 1);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4052_ = v___x_4048_;
v_isShared_4053_ = v_isSharedCheck_4063_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_res_4050_);
lean_inc(v_pos_4049_);
lean_dec(v___x_4048_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4063_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4054_ = lean_unsigned_to_nat(1u);
v___x_4055_ = lean_nat_dec_eq(v_fst_4046_, v___x_4054_);
lean_dec(v_fst_4046_);
if (v___x_4055_ == 0)
{
lean_del_object(v___x_4052_);
v___y_4033_ = v_res_4050_;
v___y_4034_ = v___x_4055_;
v___y_4035_ = v_pos_4049_;
v___y_4036_ = v_snd_4047_;
goto v___jp_4032_;
}
else
{
uint8_t v___x_4056_; 
v___x_4056_ = lean_nat_dec_eq(v_snd_4047_, v___x_4054_);
if (v___x_4056_ == 0)
{
lean_del_object(v___x_4052_);
v___y_4033_ = v_res_4050_;
v___y_4034_ = v___x_4055_;
v___y_4035_ = v_pos_4049_;
v___y_4036_ = v_snd_4047_;
goto v___jp_4032_;
}
else
{
uint8_t v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
lean_dec(v_snd_4047_);
v___x_4057_ = 1;
v___x_4058_ = l_Std_Http_Headers_empty;
v___x_4059_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4059_, 0, v_res_4050_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
lean_ctor_set_uint8(v___x_4059_, sizeof(void*)*2, v___x_4057_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 1, v___x_4059_);
v___x_4061_ = v___x_4052_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_pos_4049_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
else
{
lean_object* v_pos_4064_; lean_object* v_err_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v_snd_4047_);
lean_dec(v_fst_4046_);
v_pos_4064_ = lean_ctor_get(v___x_4048_, 0);
v_err_4065_ = lean_ctor_get(v___x_4048_, 1);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4048_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_err_4065_);
lean_inc(v_pos_4064_);
lean_dec(v___x_4048_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_pos_4064_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_err_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_4117_, v_a_4118_);
lean_dec_ref(v_limits_4117_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_pos_4123_; lean_object* v_res_4124_; lean_object* v___x_4154_; 
v___x_4154_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4121_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_pos_4155_; lean_object* v_res_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4186_; 
v_pos_4155_ = lean_ctor_get(v___x_4154_, 0);
v_res_4156_ = lean_ctor_get(v___x_4154_, 1);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4158_ = v___x_4154_;
v_isShared_4159_ = v_isSharedCheck_4186_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_res_4156_);
lean_inc(v_pos_4155_);
lean_dec(v___x_4154_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4186_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v_array_4160_; lean_object* v_idx_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; 
v_array_4160_ = lean_ctor_get(v_pos_4155_, 0);
v_idx_4161_ = lean_ctor_get(v_pos_4155_, 1);
v___x_4162_ = lean_byte_array_size(v_array_4160_);
v___x_4163_ = lean_nat_dec_lt(v_idx_4161_, v___x_4162_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4166_; 
lean_dec(v_res_4156_);
v___x_4164_ = lean_box(0);
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 1);
lean_ctor_set(v___x_4158_, 1, v___x_4164_);
v___x_4166_ = v___x_4158_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_pos_4155_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
else
{
uint8_t v___x_4168_; uint8_t v_got_4169_; uint8_t v___x_4170_; 
v___x_4168_ = 32;
v_got_4169_ = lean_byte_array_fget(v_array_4160_, v_idx_4161_);
v___x_4170_ = lean_uint8_dec_eq(v_got_4169_, v___x_4168_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
lean_dec(v_res_4156_);
v___x_4171_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 1);
lean_ctor_set(v___x_4158_, 1, v___x_4171_);
v___x_4173_ = v___x_4158_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_pos_4155_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
else
{
lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4183_; 
lean_inc(v_idx_4161_);
lean_inc_ref(v_array_4160_);
lean_del_object(v___x_4158_);
v_isSharedCheck_4183_ = !lean_is_exclusive(v_pos_4155_);
if (v_isSharedCheck_4183_ == 0)
{
lean_object* v_unused_4184_; lean_object* v_unused_4185_; 
v_unused_4184_ = lean_ctor_get(v_pos_4155_, 1);
lean_dec(v_unused_4184_);
v_unused_4185_ = lean_ctor_get(v_pos_4155_, 0);
lean_dec(v_unused_4185_);
v___x_4176_ = v_pos_4155_;
v_isShared_4177_ = v_isSharedCheck_4183_;
goto v_resetjp_4175_;
}
else
{
lean_dec(v_pos_4155_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4183_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4181_; 
v___x_4178_ = lean_unsigned_to_nat(1u);
v___x_4179_ = lean_nat_add(v_idx_4161_, v___x_4178_);
lean_dec(v_idx_4161_);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 1, v___x_4179_);
v___x_4181_ = v___x_4176_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_array_4160_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
v_pos_4123_ = v___x_4181_;
v_res_4124_ = v_res_4156_;
goto v___jp_4122_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_pos_4187_; lean_object* v_res_4188_; 
v_pos_4187_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_pos_4187_);
v_res_4188_ = lean_ctor_get(v___x_4154_, 1);
lean_inc(v_res_4188_);
lean_dec_ref_known(v___x_4154_, 2);
v_pos_4123_ = v_pos_4187_;
v_res_4124_ = v_res_4188_;
goto v___jp_4122_;
}
else
{
lean_object* v_pos_4189_; lean_object* v_err_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
v_pos_4189_ = lean_ctor_get(v___x_4154_, 0);
v_err_4190_ = lean_ctor_get(v___x_4154_, 1);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4154_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_err_4190_);
lean_inc(v_pos_4189_);
lean_dec(v___x_4154_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_pos_4189_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_err_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
v___jp_4122_:
{
lean_object* v_fst_4125_; lean_object* v_snd_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4153_; 
v_fst_4125_ = lean_ctor_get(v_res_4124_, 0);
v_snd_4126_ = lean_ctor_get(v_res_4124_, 1);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_res_4124_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4128_ = v_res_4124_;
v_isShared_4129_ = v_isSharedCheck_4153_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_snd_4126_);
lean_inc(v_fst_4125_);
lean_dec(v_res_4124_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4153_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; 
v___x_4130_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4120_, v_pos_4123_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_pos_4131_; lean_object* v_res_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4143_; 
v_pos_4131_ = lean_ctor_get(v___x_4130_, 0);
v_res_4132_ = lean_ctor_get(v___x_4130_, 1);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4134_ = v___x_4130_;
v_isShared_4135_ = v_isSharedCheck_4143_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_res_4132_);
lean_inc(v_pos_4131_);
lean_dec(v___x_4130_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4143_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4136_ = l_Std_Http_Version_ofNumber_x3f(v_fst_4125_, v_snd_4126_);
lean_dec(v_snd_4126_);
lean_dec(v_fst_4125_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 1, v___x_4136_);
lean_ctor_set(v___x_4128_, 0, v_res_4132_);
v___x_4138_ = v___x_4128_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_res_4132_);
lean_ctor_set(v_reuseFailAlloc_4142_, 1, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4140_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 1, v___x_4138_);
v___x_4140_ = v___x_4134_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_pos_4131_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
lean_object* v_pos_4144_; lean_object* v_err_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_del_object(v___x_4128_);
lean_dec(v_snd_4126_);
lean_dec(v_fst_4125_);
v_pos_4144_ = lean_ctor_get(v___x_4130_, 0);
v_err_4145_ = lean_ctor_get(v___x_4130_, 1);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4130_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_err_4145_);
lean_inc(v_pos_4144_);
lean_dec(v___x_4130_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_pos_4144_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v_err_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_4198_, v_a_4199_);
lean_dec_ref(v_limits_4198_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object* v_limits_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v_maxTrailerHeaders_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_maxTrailerHeaders_4203_ = lean_ctor_get(v_limits_4201_, 17);
lean_inc(v_maxTrailerHeaders_4203_);
v___x_4204_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_4204_, 0, v_limits_4201_);
v___x_4205_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_4204_, v_maxTrailerHeaders_4203_, v_a_4202_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_pos_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v_pos_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_pos_4206_);
lean_dec_ref_known(v___x_4205_, 2);
v___x_4207_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4208_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4207_, v_pos_4206_);
return v___x_4208_;
}
else
{
lean_object* v_pos_4209_; lean_object* v_err_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
v_pos_4209_ = lean_ctor_get(v___x_4205_, 0);
v_err_4210_ = lean_ctor_get(v___x_4205_, 1);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4205_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_err_4210_);
lean_inc(v_pos_4209_);
lean_dec(v___x_4205_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_pos_4209_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_err_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
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
