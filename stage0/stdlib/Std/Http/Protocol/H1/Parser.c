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
lean_object* v_pos_478_; lean_object* v_err_479_; lean_object* v___x_507_; 
lean_inc_ref(v_a_476_);
v___x_507_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hexDigit(v_a_476_);
if (lean_obj_tag(v___x_507_) == 0)
{
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_pos_508_; lean_object* v_res_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_526_; 
lean_dec_ref(v_a_476_);
v_pos_508_ = lean_ctor_get(v___x_507_, 0);
v_res_509_ = lean_ctor_get(v___x_507_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_526_ == 0)
{
v___x_511_ = v___x_507_;
v_isShared_512_ = v_isSharedCheck_526_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_res_509_);
lean_inc(v_pos_508_);
lean_dec(v___x_507_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_526_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_513_ = lean_unsigned_to_nat(16u);
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_count_475_, v___x_514_);
lean_dec(v_count_475_);
v___x_516_ = lean_nat_dec_lt(v___x_513_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_del_object(v___x_511_);
v___x_517_ = lean_nat_mul(v_acc_474_, v___x_513_);
lean_dec(v_acc_474_);
v___x_518_ = lean_unbox(v_res_509_);
lean_dec(v_res_509_);
v___x_519_ = lean_uint8_to_nat(v___x_518_);
v___x_520_ = lean_nat_add(v___x_517_, v___x_519_);
lean_dec(v___x_517_);
v_acc_474_ = v___x_520_;
v_count_475_ = v___x_515_;
v_a_476_ = v_pos_508_;
goto _start;
}
else
{
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec(v___x_515_);
lean_dec(v_res_509_);
lean_dec(v_acc_474_);
v___x_522_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__3));
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 1);
lean_ctor_set(v___x_511_, 1, v___x_522_);
v___x_524_ = v___x_511_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_pos_508_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_pos_527_; lean_object* v_err_528_; 
v_pos_527_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_pos_527_);
v_err_528_ = lean_ctor_get(v___x_507_, 1);
lean_inc(v_err_528_);
lean_dec_ref_known(v___x_507_, 2);
v_pos_478_ = v_pos_527_;
v_err_479_ = v_err_528_;
goto v___jp_477_;
}
}
else
{
lean_object* v_err_529_; 
v_err_529_ = lean_ctor_get(v___x_507_, 1);
lean_inc(v_err_529_);
lean_dec_ref_known(v___x_507_, 2);
lean_inc_ref(v_a_476_);
v_pos_478_ = v_a_476_;
v_err_479_ = v_err_529_;
goto v___jp_477_;
}
v___jp_477_:
{
lean_object* v_idx_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_505_; 
v_idx_480_ = lean_ctor_get(v_a_476_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_a_476_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_a_476_, 0);
lean_dec(v_unused_506_);
v___x_482_ = v_a_476_;
v_isShared_483_ = v_isSharedCheck_505_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_idx_480_);
lean_dec(v_a_476_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_505_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_array_484_; lean_object* v_idx_485_; uint8_t v___x_486_; 
v_array_484_ = lean_ctor_get(v_pos_478_, 0);
v_idx_485_ = lean_ctor_get(v_pos_478_, 1);
v___x_486_ = lean_nat_dec_eq(v_idx_480_, v_idx_485_);
lean_dec(v_idx_480_);
if (v___x_486_ == 0)
{
lean_object* v___x_488_; 
lean_dec(v_count_475_);
lean_dec(v_acc_474_);
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 1);
lean_ctor_set(v___x_482_, 1, v_err_479_);
lean_ctor_set(v___x_482_, 0, v_pos_478_);
v___x_488_ = v___x_482_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_pos_478_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_err_479_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
else
{
lean_object* v___x_490_; uint8_t v___x_491_; 
lean_dec(v_err_479_);
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = lean_nat_dec_eq(v_count_475_, v___x_490_);
lean_dec(v_count_475_);
if (v___x_491_ == 0)
{
lean_object* v___x_493_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v_acc_474_);
lean_ctor_set(v___x_482_, 0, v_pos_478_);
v___x_493_ = v___x_482_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_pos_478_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_acc_474_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v___x_495_; uint8_t v___x_496_; 
lean_dec(v_acc_474_);
v___x_495_ = lean_byte_array_size(v_array_484_);
v___x_496_ = lean_nat_dec_lt(v_idx_485_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_box(0);
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 1);
lean_ctor_set(v___x_482_, 1, v___x_497_);
lean_ctor_set(v___x_482_, 0, v_pos_478_);
v___x_499_ = v___x_482_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_pos_478_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go___closed__1));
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 1);
lean_ctor_set(v___x_482_, 1, v___x_501_);
lean_ctor_set(v___x_482_, 0, v_pos_478_);
v___x_503_ = v___x_482_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_pos_478_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(lean_object* v_a_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex_go(v___x_531_, v___x_531_, v_a_530_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__0));
v___x_535_ = lean_string_to_utf8(v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(lean_object* v_a_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__1);
v___x_544_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_543_, v_a_542_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_pos_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_606_; 
v_pos_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_544_, 1);
lean_dec(v_unused_607_);
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_606_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_pos_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_606_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_array_554_; lean_object* v_idx_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_array_554_ = lean_ctor_get(v_pos_545_, 0);
v_idx_555_ = lean_ctor_get(v_pos_545_, 1);
v___x_556_ = lean_byte_array_size(v_array_554_);
v___x_557_ = lean_nat_dec_lt(v_idx_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_del_object(v___x_547_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_559_, 0, v_pos_545_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
return v___x_559_;
}
else
{
uint8_t v_c_560_; uint8_t v___x_561_; uint8_t v___x_562_; 
v_c_560_ = lean_byte_array_fget(v_array_554_, v_idx_555_);
v___x_561_ = 48;
v___x_562_ = lean_uint8_dec_le(v___x_561_, v_c_560_);
if (v___x_562_ == 0)
{
goto v___jp_549_;
}
else
{
uint8_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = 57;
v___x_564_ = lean_uint8_dec_le(v_c_560_, v___x_563_);
if (v___x_564_ == 0)
{
goto v___jp_549_;
}
else
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_603_; 
lean_inc(v_idx_555_);
lean_inc_ref(v_array_554_);
lean_del_object(v___x_547_);
v_isSharedCheck_603_ = !lean_is_exclusive(v_pos_545_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; lean_object* v_unused_605_; 
v_unused_604_ = lean_ctor_get(v_pos_545_, 1);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_pos_545_, 0);
lean_dec(v_unused_605_);
v___x_566_ = v_pos_545_;
v_isShared_567_ = v_isSharedCheck_603_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_pos_545_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_603_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_it_x27_571_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_idx_555_, v___x_568_);
lean_dec(v_idx_555_);
lean_inc(v___x_569_);
lean_inc_ref(v_array_554_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_569_);
v_it_x27_571_ = v___x_566_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_array_554_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_569_);
v_it_x27_571_ = v_reuseFailAlloc_602_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
uint8_t v___x_572_; 
v___x_572_ = lean_nat_dec_lt(v___x_569_, v___x_556_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_569_);
lean_dec_ref(v_array_554_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v_it_x27_571_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
return v___x_574_;
}
else
{
uint8_t v___x_575_; uint8_t v_got_576_; uint8_t v___x_577_; 
v___x_575_ = 46;
v_got_576_ = lean_byte_array_fget(v_array_554_, v___x_569_);
v___x_577_ = lean_uint8_dec_eq(v_got_576_, v___x_575_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_569_);
lean_dec_ref(v_array_554_);
v___x_578_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__5));
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v_it_x27_571_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_585_; 
lean_dec_ref(v_it_x27_571_);
v___x_580_ = lean_nat_add(v___x_569_, v___x_568_);
lean_dec(v___x_569_);
lean_inc(v___x_580_);
lean_inc_ref(v_array_554_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_array_554_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_585_ = lean_nat_dec_lt(v___x_580_, v___x_556_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v___x_580_);
lean_dec_ref(v_array_554_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_581_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
return v___x_587_;
}
else
{
uint8_t v_c_588_; uint8_t v___x_589_; 
v_c_588_ = lean_byte_array_fget(v_array_554_, v___x_580_);
v___x_589_ = lean_uint8_dec_le(v___x_561_, v_c_588_);
if (v___x_589_ == 0)
{
lean_dec(v___x_580_);
lean_dec_ref(v_array_554_);
goto v___jp_582_;
}
else
{
uint8_t v___x_590_; 
v___x_590_ = lean_uint8_dec_le(v_c_588_, v___x_563_);
if (v___x_590_ == 0)
{
lean_dec(v___x_580_);
lean_dec_ref(v_array_554_);
goto v___jp_582_;
}
else
{
lean_object* v___x_591_; uint32_t v___x_592_; lean_object* v___x_593_; lean_object* v_it_x27_594_; uint32_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec_ref_known(v___x_581_, 2);
v___x_591_ = lean_unsigned_to_nat(48u);
v___x_592_ = lean_uint8_to_uint32(v_c_560_);
v___x_593_ = lean_nat_add(v___x_580_, v___x_568_);
lean_dec(v___x_580_);
v_it_x27_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_594_, 0, v_array_554_);
lean_ctor_set(v_it_x27_594_, 1, v___x_593_);
v___x_595_ = lean_uint8_to_uint32(v_c_588_);
v___x_596_ = lean_uint32_to_nat(v___x_592_);
v___x_597_ = lean_nat_sub(v___x_596_, v___x_591_);
lean_dec(v___x_596_);
v___x_598_ = lean_uint32_to_nat(v___x_595_);
v___x_599_ = lean_nat_sub(v___x_598_, v___x_591_);
lean_dec(v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_it_x27_594_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
return v___x_601_;
}
}
}
v___jp_582_:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_581_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
return v___x_584_;
}
}
}
}
}
}
}
}
v___jp_549_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 1);
lean_ctor_set(v___x_547_, 1, v___x_550_);
v___x_552_ = v___x_547_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_pos_545_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_pos_608_; lean_object* v_err_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_pos_608_ = lean_ctor_get(v___x_544_, 0);
v_err_609_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_544_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_err_609_);
lean_inc(v_pos_608_);
lean_dec(v___x_544_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_pos_608_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_err_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersion(lean_object* v_a_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_res_619_; lean_object* v_pos_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_res_619_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_res_619_);
v_pos_620_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_pos_620_);
lean_dec_ref_known(v___x_618_, 2);
v_fst_621_ = lean_ctor_get(v_res_619_, 0);
lean_inc(v_fst_621_);
v_snd_622_ = lean_ctor_get(v_res_619_, 1);
lean_inc(v_snd_622_);
lean_dec(v_res_619_);
v___x_623_ = l_Std_Http_Version_ofNumber_x3f(v_fst_621_, v_snd_622_);
lean_dec(v_snd_622_);
lean_dec(v_fst_621_);
v___x_624_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_623_, v_pos_620_);
lean_dec(v___x_623_);
return v___x_624_;
}
else
{
lean_object* v_pos_625_; lean_object* v_err_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_pos_625_ = lean_ctor_get(v___x_618_, 0);
v_err_626_ = lean_ctor_get(v___x_618_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_618_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_err_626_);
lean_inc(v_pos_625_);
lean_dec(v___x_618_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_pos_625_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_err_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(lean_object* v_a_634_, lean_object* v_f_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = lean_apply_1(v_a_634_, v___y_636_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_pos_638_; lean_object* v_res_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
v_pos_638_ = lean_ctor_get(v___x_637_, 0);
v_res_639_ = lean_ctor_get(v___x_637_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v___x_637_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_res_639_);
lean_inc(v_pos_638_);
lean_dec(v___x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_apply_1(v_f_635_, v_res_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_pos_638_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_pos_648_; lean_object* v_err_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_f_635_);
v_pos_648_ = lean_ctor_get(v___x_637_, 0);
v_err_649_ = lean_ctor_get(v___x_637_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_637_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_err_649_);
lean_inc(v_pos_648_);
lean_dec(v___x_637_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_pos_648_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_err_649_);
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
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0(lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_a_659_, lean_object* v_f_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v_a_659_, v_f_660_, v___y_661_);
return v___x_662_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(lean_object* v_x_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = 9;
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0___boxed(lean_object* v_x_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__0(v_x_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(lean_object* v_x_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = 32;
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1___boxed(lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__1(v_x_670_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(lean_object* v_x_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = 28;
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2___boxed(lean_object* v_x_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__2(v_x_675_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(lean_object* v_x_678_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = 1;
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3___boxed(lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__3(v_x_680_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(lean_object* v_x_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = 5;
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4___boxed(lean_object* v_x_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__4(v_x_685_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(lean_object* v_x_688_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = 4;
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5___boxed(lean_object* v_x_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__5(v_x_690_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(lean_object* v_x_693_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = 10;
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6___boxed(lean_object* v_x_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__6(v_x_695_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(lean_object* v_x_698_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = 12;
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7___boxed(lean_object* v_x_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__7(v_x_700_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(lean_object* v_x_703_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = 14;
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8___boxed(lean_object* v_x_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__8(v_x_705_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(lean_object* v_x_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = 16;
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9___boxed(lean_object* v_x_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__9(v_x_710_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(lean_object* v_x_713_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = 18;
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10___boxed(lean_object* v_x_715_){
_start:
{
uint8_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__10(v_x_715_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(lean_object* v_x_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = 20;
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11___boxed(lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__11(v_x_720_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(lean_object* v_x_723_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = 23;
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12___boxed(lean_object* v_x_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__12(v_x_725_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(lean_object* v_x_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = 22;
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13___boxed(lean_object* v_x_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__13(v_x_730_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(lean_object* v_x_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = 25;
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14___boxed(lean_object* v_x_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__14(v_x_735_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(lean_object* v_x_738_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = 29;
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15___boxed(lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__15(v_x_740_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(lean_object* v_x_743_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = 33;
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16___boxed(lean_object* v_x_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__16(v_x_745_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(lean_object* v_x_748_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = 35;
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17___boxed(lean_object* v_x_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__17(v_x_750_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(lean_object* v_x_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = 38;
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18___boxed(lean_object* v_x_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__18(v_x_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(lean_object* v_x_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = 39;
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19___boxed(lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__19(v_x_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(lean_object* v_x_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = 37;
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21___boxed(lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__21(v_x_765_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(lean_object* v_x_768_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = 36;
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20___boxed(lean_object* v_x_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__20(v_x_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(lean_object* v_x_773_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = 34;
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22___boxed(lean_object* v_x_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__22(v_x_775_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(lean_object* v_x_778_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = 30;
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23___boxed(lean_object* v_x_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__23(v_x_780_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(lean_object* v_x_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = 26;
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24___boxed(lean_object* v_x_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__24(v_x_785_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(lean_object* v_x_788_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = 24;
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25___boxed(lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__25(v_x_790_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(lean_object* v_x_793_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = 27;
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26___boxed(lean_object* v_x_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__26(v_x_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(lean_object* v_x_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = 21;
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27___boxed(lean_object* v_x_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__27(v_x_800_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(lean_object* v_x_803_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = 19;
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28___boxed(lean_object* v_x_805_){
_start:
{
uint8_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__28(v_x_805_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(lean_object* v_x_808_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = 17;
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29___boxed(lean_object* v_x_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__29(v_x_810_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(lean_object* v_x_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = 15;
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30___boxed(lean_object* v_x_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__30(v_x_815_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(lean_object* v_x_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = 13;
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31___boxed(lean_object* v_x_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__31(v_x_820_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(lean_object* v_x_823_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = 11;
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32___boxed(lean_object* v_x_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__32(v_x_825_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(lean_object* v_x_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = 6;
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33___boxed(lean_object* v_x_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__33(v_x_830_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(lean_object* v_x_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = 3;
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34___boxed(lean_object* v_x_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__34(v_x_835_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(lean_object* v_x_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = 2;
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35___boxed(lean_object* v_x_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__35(v_x_840_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(lean_object* v_x_843_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = 31;
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36___boxed(lean_object* v_x_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__36(v_x_845_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(lean_object* v_x_848_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = 0;
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37___boxed(lean_object* v_x_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__37(v_x_850_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(lean_object* v_x_853_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = 7;
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38___boxed(lean_object* v_x_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__38(v_x_855_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(lean_object* v_x_858_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = 8;
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39___boxed(lean_object* v_x_860_){
_start:
{
uint8_t v_res_861_; lean_object* v_r_862_; 
v_res_861_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___lam__39(v_x_860_);
v_r_862_ = lean_box(v_res_861_);
return v_r_862_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__22));
v___x_888_ = lean_string_to_utf8(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__23);
v___x_890_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__26));
v___x_894_ = lean_string_to_utf8(v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__27);
v___x_896_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__29));
v___x_899_ = lean_string_to_utf8(v___x_898_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__30);
v___x_901_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__33));
v___x_905_ = lean_string_to_utf8(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__34);
v___x_907_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__36));
v___x_910_ = lean_string_to_utf8(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__37);
v___x_912_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__40));
v___x_916_ = lean_string_to_utf8(v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__41);
v___x_918_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__43));
v___x_921_ = lean_string_to_utf8(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__44);
v___x_923_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__47));
v___x_927_ = lean_string_to_utf8(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__48);
v___x_929_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__50));
v___x_932_ = lean_string_to_utf8(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__51);
v___x_934_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__54));
v___x_938_ = lean_string_to_utf8(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__55);
v___x_940_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__57));
v___x_943_ = lean_string_to_utf8(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__58);
v___x_945_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__61));
v___x_949_ = lean_string_to_utf8(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__62);
v___x_951_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__64));
v___x_954_ = lean_string_to_utf8(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__65);
v___x_956_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__68));
v___x_960_ = lean_string_to_utf8(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__69);
v___x_962_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__71));
v___x_965_ = lean_string_to_utf8(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__72);
v___x_967_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__75));
v___x_971_ = lean_string_to_utf8(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__76);
v___x_973_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__78));
v___x_976_ = lean_string_to_utf8(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__79);
v___x_978_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__82));
v___x_982_ = lean_string_to_utf8(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__83);
v___x_984_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__85));
v___x_987_ = lean_string_to_utf8(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__86);
v___x_989_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__89));
v___x_993_ = lean_string_to_utf8(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__90);
v___x_995_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__92));
v___x_998_ = lean_string_to_utf8(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__93);
v___x_1000_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__96));
v___x_1004_ = lean_string_to_utf8(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__97);
v___x_1006_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__99));
v___x_1009_ = lean_string_to_utf8(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__100);
v___x_1011_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__103));
v___x_1015_ = lean_string_to_utf8(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__104);
v___x_1017_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__106));
v___x_1020_ = lean_string_to_utf8(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__107);
v___x_1022_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__110));
v___x_1026_ = lean_string_to_utf8(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__111);
v___x_1028_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__113));
v___x_1031_ = lean_string_to_utf8(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__114);
v___x_1033_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__117));
v___x_1037_ = lean_string_to_utf8(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__118);
v___x_1039_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__120));
v___x_1042_ = lean_string_to_utf8(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__121);
v___x_1044_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__124));
v___x_1048_ = lean_string_to_utf8(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__125);
v___x_1050_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__127));
v___x_1053_ = lean_string_to_utf8(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__128);
v___x_1055_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__131));
v___x_1059_ = lean_string_to_utf8(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__132);
v___x_1061_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__134));
v___x_1064_ = lean_string_to_utf8(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__135);
v___x_1066_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__138));
v___x_1070_ = lean_string_to_utf8(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__139);
v___x_1072_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__141));
v___x_1075_ = lean_string_to_utf8(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__142);
v___x_1077_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__145));
v___x_1081_ = lean_string_to_utf8(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__146);
v___x_1083_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__148));
v___x_1086_ = lean_string_to_utf8(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__149);
v___x_1088_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__152));
v___x_1092_ = lean_string_to_utf8(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__153);
v___x_1094_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__155));
v___x_1097_ = lean_string_to_utf8(v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__156);
v___x_1099_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__159));
v___x_1103_ = lean_string_to_utf8(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__160);
v___x_1105_ = lean_alloc_closure((void*)(l_Std_Internal_Parsec_ByteArray_skipBytes___boxed), 2, 1);
lean_closure_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(lean_object* v_a_1106_){
_start:
{
lean_object* v___f_1107_; lean_object* v___f_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; lean_object* v___f_1118_; lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v_idx_1129_; lean_object* v___y_1130_; lean_object* v_pos_1131_; lean_object* v_idx_1132_; lean_object* v_idx_1167_; lean_object* v___y_1168_; lean_object* v_pos_1169_; lean_object* v_idx_1170_; lean_object* v___f_1185_; lean_object* v_idx_1187_; lean_object* v___y_1188_; lean_object* v_pos_1189_; lean_object* v_idx_1190_; lean_object* v_idx_1206_; lean_object* v___y_1207_; lean_object* v_pos_1208_; lean_object* v_idx_1209_; lean_object* v___f_1224_; lean_object* v_idx_1226_; lean_object* v___y_1227_; lean_object* v_pos_1228_; lean_object* v_idx_1229_; lean_object* v_idx_1245_; lean_object* v___y_1246_; lean_object* v_pos_1247_; lean_object* v_idx_1248_; lean_object* v___f_1263_; lean_object* v_idx_1265_; lean_object* v___y_1266_; lean_object* v_pos_1267_; lean_object* v_idx_1268_; lean_object* v_idx_1284_; lean_object* v___y_1285_; lean_object* v_pos_1286_; lean_object* v_idx_1287_; lean_object* v___f_1302_; lean_object* v_idx_1304_; lean_object* v___y_1305_; lean_object* v_pos_1306_; lean_object* v_idx_1307_; lean_object* v_idx_1323_; lean_object* v___y_1324_; lean_object* v_pos_1325_; lean_object* v_idx_1326_; lean_object* v___f_1341_; lean_object* v_idx_1343_; lean_object* v___y_1344_; lean_object* v_pos_1345_; lean_object* v_idx_1346_; lean_object* v_idx_1362_; lean_object* v___y_1363_; lean_object* v_pos_1364_; lean_object* v_idx_1365_; lean_object* v___f_1380_; lean_object* v_idx_1382_; lean_object* v___y_1383_; lean_object* v_pos_1384_; lean_object* v_idx_1385_; lean_object* v_idx_1401_; lean_object* v___y_1402_; lean_object* v_pos_1403_; lean_object* v_idx_1404_; lean_object* v___f_1419_; lean_object* v_idx_1421_; lean_object* v___y_1422_; lean_object* v_pos_1423_; lean_object* v_idx_1424_; lean_object* v_idx_1440_; lean_object* v___y_1441_; lean_object* v_pos_1442_; lean_object* v_idx_1443_; lean_object* v___f_1458_; lean_object* v_idx_1460_; lean_object* v___y_1461_; lean_object* v_pos_1462_; lean_object* v_idx_1463_; lean_object* v_idx_1479_; lean_object* v___y_1480_; lean_object* v_pos_1481_; lean_object* v_idx_1482_; lean_object* v___f_1497_; lean_object* v_idx_1499_; lean_object* v___y_1500_; lean_object* v_pos_1501_; lean_object* v_idx_1502_; lean_object* v_idx_1518_; lean_object* v___y_1519_; lean_object* v_pos_1520_; lean_object* v_idx_1521_; lean_object* v___f_1536_; lean_object* v_idx_1538_; lean_object* v___y_1539_; lean_object* v_pos_1540_; lean_object* v_idx_1541_; lean_object* v_idx_1557_; lean_object* v___y_1558_; lean_object* v_pos_1559_; lean_object* v_idx_1560_; lean_object* v___f_1575_; lean_object* v_idx_1577_; lean_object* v___y_1578_; lean_object* v_pos_1579_; lean_object* v_idx_1580_; lean_object* v_idx_1596_; lean_object* v___y_1597_; lean_object* v_pos_1598_; lean_object* v_idx_1599_; lean_object* v___f_1614_; lean_object* v_idx_1616_; lean_object* v___y_1617_; lean_object* v_pos_1618_; lean_object* v_idx_1619_; lean_object* v_idx_1635_; lean_object* v___y_1636_; lean_object* v_pos_1637_; lean_object* v_idx_1638_; lean_object* v___f_1653_; lean_object* v_idx_1655_; lean_object* v___y_1656_; lean_object* v_pos_1657_; lean_object* v_idx_1658_; lean_object* v_idx_1674_; lean_object* v___y_1675_; lean_object* v_pos_1676_; lean_object* v_idx_1677_; lean_object* v___f_1692_; lean_object* v_idx_1694_; lean_object* v___y_1695_; lean_object* v_pos_1696_; lean_object* v_idx_1697_; lean_object* v_idx_1713_; lean_object* v___y_1714_; lean_object* v_pos_1715_; lean_object* v_idx_1716_; lean_object* v___f_1731_; lean_object* v_idx_1733_; lean_object* v___y_1734_; lean_object* v_pos_1735_; lean_object* v_idx_1736_; lean_object* v_idx_1752_; lean_object* v___y_1753_; lean_object* v_pos_1754_; lean_object* v_idx_1755_; lean_object* v___f_1770_; lean_object* v_idx_1772_; lean_object* v___y_1773_; lean_object* v_pos_1774_; lean_object* v_idx_1775_; lean_object* v_idx_1791_; lean_object* v___y_1792_; lean_object* v_pos_1793_; lean_object* v_idx_1794_; lean_object* v___f_1809_; lean_object* v_idx_1811_; lean_object* v___y_1812_; lean_object* v_pos_1813_; lean_object* v_idx_1814_; lean_object* v_idx_1830_; lean_object* v___y_1831_; lean_object* v_pos_1832_; lean_object* v_idx_1833_; lean_object* v___f_1848_; lean_object* v_idx_1850_; lean_object* v___y_1851_; lean_object* v_pos_1852_; lean_object* v_idx_1853_; lean_object* v_idx_1869_; lean_object* v___y_1870_; lean_object* v_pos_1871_; lean_object* v_idx_1872_; lean_object* v___f_1887_; lean_object* v_idx_1889_; lean_object* v___y_1890_; lean_object* v_pos_1891_; lean_object* v_idx_1892_; lean_object* v___y_1908_; lean_object* v_pos_1909_; lean_object* v___f_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___f_1107_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__0));
v___f_1108_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__1));
v___f_1109_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__2));
v___f_1110_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__3));
v___f_1111_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__4));
v___f_1112_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__5));
v___f_1113_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__6));
v___f_1114_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__7));
v___f_1115_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__8));
v___f_1116_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__9));
v___f_1117_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__10));
v___f_1118_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__11));
v___f_1119_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__12));
v___f_1120_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__13));
v___f_1121_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__14));
v___f_1122_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__15));
v___f_1123_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__16));
v___f_1124_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__17));
v___f_1125_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__18));
v___f_1126_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__19));
v___f_1127_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___f_1185_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__25));
v___f_1224_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__32));
v___f_1263_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__39));
v___f_1302_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__46));
v___f_1341_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__53));
v___f_1380_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__60));
v___f_1419_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__67));
v___f_1458_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__74));
v___f_1497_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__81));
v___f_1536_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__88));
v___f_1575_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__95));
v___f_1614_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__102));
v___f_1653_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__109));
v___f_1692_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__116));
v___f_1731_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__123));
v___f_1770_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__130));
v___f_1809_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__137));
v___f_1848_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__144));
v___f_1887_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__151));
v___f_1926_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__158));
v___x_1927_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__161);
lean_inc_ref(v_a_1106_);
v___x_1928_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1927_, v___f_1926_, v_a_1106_);
if (lean_obj_tag(v___x_1928_) == 0)
{
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_dec_ref(v_a_1106_);
return v___x_1928_;
}
else
{
lean_object* v_pos_1929_; 
v_pos_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_pos_1929_);
v___y_1908_ = v___x_1928_;
v_pos_1909_ = v_pos_1929_;
goto v___jp_1907_;
}
}
else
{
lean_object* v_err_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_err_1930_ = lean_ctor_get(v___x_1928_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v___x_1928_, 0);
lean_dec(v_unused_1938_);
v___x_1932_ = v___x_1928_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_err_1930_);
lean_dec(v___x_1928_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
lean_inc_ref(v_a_1106_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v_a_1106_);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1106_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_err_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_inc_ref(v_a_1106_);
v___y_1908_ = v___x_1935_;
v_pos_1909_ = v_a_1106_;
goto v___jp_1907_;
}
}
}
v___jp_1128_:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_eq(v_idx_1129_, v_idx_1132_);
lean_dec(v_idx_1132_);
lean_dec(v_idx_1129_);
if (v___x_1133_ == 0)
{
lean_dec_ref(v_pos_1131_);
return v___y_1130_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_snd_1137_; lean_object* v_snd_1138_; uint8_t v___x_1139_; 
lean_dec_ref(v___y_1130_);
v___x_1134_ = lean_unsigned_to_nat(64u);
v___x_1135_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pos_1131_);
v___x_1136_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1127_, v___x_1134_, v___x_1135_, v_pos_1131_);
v_snd_1137_ = lean_ctor_get(v___x_1136_, 1);
lean_inc(v_snd_1137_);
v_snd_1138_ = lean_ctor_get(v_snd_1137_, 1);
v___x_1139_ = lean_unbox(v_snd_1138_);
if (v___x_1139_ == 0)
{
lean_object* v_fst_1140_; lean_object* v_fst_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1154_; 
v_fst_1140_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_fst_1140_);
lean_dec_ref(v___x_1136_);
v_fst_1141_ = lean_ctor_get(v_snd_1137_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_snd_1137_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_snd_1137_, 1);
lean_dec(v_unused_1155_);
v___x_1143_ = v_snd_1137_;
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_fst_1141_);
lean_dec(v_snd_1137_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_nat_dec_eq(v_fst_1140_, v___x_1135_);
lean_dec(v_fst_1140_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec_ref(v_pos_1131_);
v___x_1146_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__21));
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 1);
lean_ctor_set(v___x_1143_, 1, v___x_1146_);
v___x_1148_ = v___x_1143_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_fst_1141_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec(v_fst_1141_);
v___x_1150_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 1);
lean_ctor_set(v___x_1143_, 1, v___x_1150_);
lean_ctor_set(v___x_1143_, 0, v_pos_1131_);
v___x_1152_ = v___x_1143_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_pos_1131_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_fst_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v___x_1136_);
lean_dec_ref(v_pos_1131_);
v_fst_1156_ = lean_ctor_get(v_snd_1137_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_snd_1137_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v_snd_1137_, 1);
lean_dec(v_unused_1165_);
v___x_1158_ = v_snd_1137_;
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_fst_1156_);
lean_dec(v_snd_1137_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = lean_box(0);
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 1);
lean_ctor_set(v___x_1158_, 1, v___x_1160_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_fst_1156_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
v___jp_1166_:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_nat_dec_eq(v_idx_1167_, v_idx_1170_);
lean_dec(v_idx_1167_);
if (v___x_1171_ == 0)
{
lean_dec(v_idx_1170_);
lean_dec_ref(v_pos_1169_);
return v___y_1168_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec_ref(v___y_1168_);
v___x_1172_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__24);
lean_inc_ref(v_pos_1169_);
v___x_1173_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1172_, v___f_1126_, v_pos_1169_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_dec_ref(v_pos_1169_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_dec(v_idx_1170_);
return v___x_1173_;
}
else
{
lean_object* v_pos_1174_; lean_object* v_idx_1175_; 
v_pos_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_pos_1174_);
v_idx_1175_ = lean_ctor_get(v_pos_1174_, 1);
lean_inc(v_idx_1175_);
v_idx_1129_ = v_idx_1170_;
v___y_1130_ = v___x_1173_;
v_pos_1131_ = v_pos_1174_;
v_idx_1132_ = v_idx_1175_;
goto v___jp_1128_;
}
}
else
{
lean_object* v_err_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_err_1176_ = lean_ctor_get(v___x_1173_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v___x_1173_, 0);
lean_dec(v_unused_1184_);
v___x_1178_ = v___x_1173_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_err_1176_);
lean_dec(v___x_1173_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
lean_inc_ref(v_pos_1169_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v_pos_1169_);
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_pos_1169_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_err_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_inc(v_idx_1170_);
v_idx_1129_ = v_idx_1170_;
v___y_1130_ = v___x_1181_;
v_pos_1131_ = v_pos_1169_;
v_idx_1132_ = v_idx_1170_;
goto v___jp_1128_;
}
}
}
}
}
v___jp_1186_:
{
uint8_t v___x_1191_; 
v___x_1191_ = lean_nat_dec_eq(v_idx_1187_, v_idx_1190_);
lean_dec(v_idx_1187_);
if (v___x_1191_ == 0)
{
lean_dec(v_idx_1190_);
lean_dec_ref(v_pos_1189_);
return v___y_1188_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v___y_1188_);
v___x_1192_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__28);
lean_inc_ref(v_pos_1189_);
v___x_1193_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1192_, v___f_1185_, v_pos_1189_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_dec_ref(v_pos_1189_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_dec(v_idx_1190_);
return v___x_1193_;
}
else
{
lean_object* v_pos_1194_; lean_object* v_idx_1195_; 
v_pos_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_pos_1194_);
v_idx_1195_ = lean_ctor_get(v_pos_1194_, 1);
lean_inc(v_idx_1195_);
v_idx_1167_ = v_idx_1190_;
v___y_1168_ = v___x_1193_;
v_pos_1169_ = v_pos_1194_;
v_idx_1170_ = v_idx_1195_;
goto v___jp_1166_;
}
}
else
{
lean_object* v_err_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_err_1196_ = lean_ctor_get(v___x_1193_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v___x_1193_, 0);
lean_dec(v_unused_1204_);
v___x_1198_ = v___x_1193_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_err_1196_);
lean_dec(v___x_1193_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
lean_inc_ref(v_pos_1189_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v_pos_1189_);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_pos_1189_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_err_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_inc(v_idx_1190_);
v_idx_1167_ = v_idx_1190_;
v___y_1168_ = v___x_1201_;
v_pos_1169_ = v_pos_1189_;
v_idx_1170_ = v_idx_1190_;
goto v___jp_1166_;
}
}
}
}
}
v___jp_1205_:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_nat_dec_eq(v_idx_1206_, v_idx_1209_);
lean_dec(v_idx_1206_);
if (v___x_1210_ == 0)
{
lean_dec(v_idx_1209_);
lean_dec_ref(v_pos_1208_);
return v___y_1207_;
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v___y_1207_);
v___x_1211_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__31);
lean_inc_ref(v_pos_1208_);
v___x_1212_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1211_, v___f_1125_, v_pos_1208_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_dec_ref(v_pos_1208_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_dec(v_idx_1209_);
return v___x_1212_;
}
else
{
lean_object* v_pos_1213_; lean_object* v_idx_1214_; 
v_pos_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_pos_1213_);
v_idx_1214_ = lean_ctor_get(v_pos_1213_, 1);
lean_inc(v_idx_1214_);
v_idx_1187_ = v_idx_1209_;
v___y_1188_ = v___x_1212_;
v_pos_1189_ = v_pos_1213_;
v_idx_1190_ = v_idx_1214_;
goto v___jp_1186_;
}
}
else
{
lean_object* v_err_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_err_1215_ = lean_ctor_get(v___x_1212_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1212_, 0);
lean_dec(v_unused_1223_);
v___x_1217_ = v___x_1212_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_err_1215_);
lean_dec(v___x_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
lean_inc_ref(v_pos_1208_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v_pos_1208_);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_pos_1208_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_err_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_inc(v_idx_1209_);
v_idx_1187_ = v_idx_1209_;
v___y_1188_ = v___x_1220_;
v_pos_1189_ = v_pos_1208_;
v_idx_1190_ = v_idx_1209_;
goto v___jp_1186_;
}
}
}
}
}
v___jp_1225_:
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_eq(v_idx_1226_, v_idx_1229_);
lean_dec(v_idx_1226_);
if (v___x_1230_ == 0)
{
lean_dec(v_idx_1229_);
lean_dec_ref(v_pos_1228_);
return v___y_1227_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec_ref(v___y_1227_);
v___x_1231_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__35);
lean_inc_ref(v_pos_1228_);
v___x_1232_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1231_, v___f_1224_, v_pos_1228_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_dec_ref(v_pos_1228_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_dec(v_idx_1229_);
return v___x_1232_;
}
else
{
lean_object* v_pos_1233_; lean_object* v_idx_1234_; 
v_pos_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_pos_1233_);
v_idx_1234_ = lean_ctor_get(v_pos_1233_, 1);
lean_inc(v_idx_1234_);
v_idx_1206_ = v_idx_1229_;
v___y_1207_ = v___x_1232_;
v_pos_1208_ = v_pos_1233_;
v_idx_1209_ = v_idx_1234_;
goto v___jp_1205_;
}
}
else
{
lean_object* v_err_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_err_1235_ = lean_ctor_get(v___x_1232_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1243_);
v___x_1237_ = v___x_1232_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_err_1235_);
lean_dec(v___x_1232_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
lean_inc_ref(v_pos_1228_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_pos_1228_);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_pos_1228_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_err_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_inc(v_idx_1229_);
v_idx_1206_ = v_idx_1229_;
v___y_1207_ = v___x_1240_;
v_pos_1208_ = v_pos_1228_;
v_idx_1209_ = v_idx_1229_;
goto v___jp_1205_;
}
}
}
}
}
v___jp_1244_:
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_nat_dec_eq(v_idx_1245_, v_idx_1248_);
lean_dec(v_idx_1245_);
if (v___x_1249_ == 0)
{
lean_dec(v_idx_1248_);
lean_dec_ref(v_pos_1247_);
return v___y_1246_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref(v___y_1246_);
v___x_1250_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__38);
lean_inc_ref(v_pos_1247_);
v___x_1251_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1250_, v___f_1124_, v_pos_1247_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_dec_ref(v_pos_1247_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_dec(v_idx_1248_);
return v___x_1251_;
}
else
{
lean_object* v_pos_1252_; lean_object* v_idx_1253_; 
v_pos_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_pos_1252_);
v_idx_1253_ = lean_ctor_get(v_pos_1252_, 1);
lean_inc(v_idx_1253_);
v_idx_1226_ = v_idx_1248_;
v___y_1227_ = v___x_1251_;
v_pos_1228_ = v_pos_1252_;
v_idx_1229_ = v_idx_1253_;
goto v___jp_1225_;
}
}
else
{
lean_object* v_err_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_err_1254_ = lean_ctor_get(v___x_1251_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1262_);
v___x_1256_ = v___x_1251_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_err_1254_);
lean_dec(v___x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
lean_inc_ref(v_pos_1247_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v_pos_1247_);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_pos_1247_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_err_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_inc(v_idx_1248_);
v_idx_1226_ = v_idx_1248_;
v___y_1227_ = v___x_1259_;
v_pos_1228_ = v_pos_1247_;
v_idx_1229_ = v_idx_1248_;
goto v___jp_1225_;
}
}
}
}
}
v___jp_1264_:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_nat_dec_eq(v_idx_1265_, v_idx_1268_);
lean_dec(v_idx_1265_);
if (v___x_1269_ == 0)
{
lean_dec(v_idx_1268_);
lean_dec_ref(v_pos_1267_);
return v___y_1266_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v___y_1266_);
v___x_1270_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__42);
lean_inc_ref(v_pos_1267_);
v___x_1271_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1270_, v___f_1263_, v_pos_1267_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_dec_ref(v_pos_1267_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_dec(v_idx_1268_);
return v___x_1271_;
}
else
{
lean_object* v_pos_1272_; lean_object* v_idx_1273_; 
v_pos_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_pos_1272_);
v_idx_1273_ = lean_ctor_get(v_pos_1272_, 1);
lean_inc(v_idx_1273_);
v_idx_1245_ = v_idx_1268_;
v___y_1246_ = v___x_1271_;
v_pos_1247_ = v_pos_1272_;
v_idx_1248_ = v_idx_1273_;
goto v___jp_1244_;
}
}
else
{
lean_object* v_err_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_err_1274_ = lean_ctor_get(v___x_1271_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1271_, 0);
lean_dec(v_unused_1282_);
v___x_1276_ = v___x_1271_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_err_1274_);
lean_dec(v___x_1271_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
lean_inc_ref(v_pos_1267_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v_pos_1267_);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_pos_1267_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_err_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_inc(v_idx_1268_);
v_idx_1245_ = v_idx_1268_;
v___y_1246_ = v___x_1279_;
v_pos_1247_ = v_pos_1267_;
v_idx_1248_ = v_idx_1268_;
goto v___jp_1244_;
}
}
}
}
}
v___jp_1283_:
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_nat_dec_eq(v_idx_1284_, v_idx_1287_);
lean_dec(v_idx_1284_);
if (v___x_1288_ == 0)
{
lean_dec(v_idx_1287_);
lean_dec_ref(v_pos_1286_);
return v___y_1285_;
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec_ref(v___y_1285_);
v___x_1289_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__45);
lean_inc_ref(v_pos_1286_);
v___x_1290_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1289_, v___f_1123_, v_pos_1286_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_dec_ref(v_pos_1286_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_dec(v_idx_1287_);
return v___x_1290_;
}
else
{
lean_object* v_pos_1291_; lean_object* v_idx_1292_; 
v_pos_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_pos_1291_);
v_idx_1292_ = lean_ctor_get(v_pos_1291_, 1);
lean_inc(v_idx_1292_);
v_idx_1265_ = v_idx_1287_;
v___y_1266_ = v___x_1290_;
v_pos_1267_ = v_pos_1291_;
v_idx_1268_ = v_idx_1292_;
goto v___jp_1264_;
}
}
else
{
lean_object* v_err_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_err_1293_ = lean_ctor_get(v___x_1290_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v___x_1290_, 0);
lean_dec(v_unused_1301_);
v___x_1295_ = v___x_1290_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_err_1293_);
lean_dec(v___x_1290_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
lean_inc_ref(v_pos_1286_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v_pos_1286_);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_pos_1286_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_err_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_inc(v_idx_1287_);
v_idx_1265_ = v_idx_1287_;
v___y_1266_ = v___x_1298_;
v_pos_1267_ = v_pos_1286_;
v_idx_1268_ = v_idx_1287_;
goto v___jp_1264_;
}
}
}
}
}
v___jp_1303_:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_nat_dec_eq(v_idx_1304_, v_idx_1307_);
lean_dec(v_idx_1304_);
if (v___x_1308_ == 0)
{
lean_dec(v_idx_1307_);
lean_dec_ref(v_pos_1306_);
return v___y_1305_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v___y_1305_);
v___x_1309_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__49);
lean_inc_ref(v_pos_1306_);
v___x_1310_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1309_, v___f_1302_, v_pos_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_dec_ref(v_pos_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_dec(v_idx_1307_);
return v___x_1310_;
}
else
{
lean_object* v_pos_1311_; lean_object* v_idx_1312_; 
v_pos_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_pos_1311_);
v_idx_1312_ = lean_ctor_get(v_pos_1311_, 1);
lean_inc(v_idx_1312_);
v_idx_1284_ = v_idx_1307_;
v___y_1285_ = v___x_1310_;
v_pos_1286_ = v_pos_1311_;
v_idx_1287_ = v_idx_1312_;
goto v___jp_1283_;
}
}
else
{
lean_object* v_err_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_err_1313_ = lean_ctor_get(v___x_1310_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v___x_1310_, 0);
lean_dec(v_unused_1321_);
v___x_1315_ = v___x_1310_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_err_1313_);
lean_dec(v___x_1310_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
lean_inc_ref(v_pos_1306_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v_pos_1306_);
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_pos_1306_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_err_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_inc(v_idx_1307_);
v_idx_1284_ = v_idx_1307_;
v___y_1285_ = v___x_1318_;
v_pos_1286_ = v_pos_1306_;
v_idx_1287_ = v_idx_1307_;
goto v___jp_1283_;
}
}
}
}
}
v___jp_1322_:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_nat_dec_eq(v_idx_1323_, v_idx_1326_);
lean_dec(v_idx_1323_);
if (v___x_1327_ == 0)
{
lean_dec(v_idx_1326_);
lean_dec_ref(v_pos_1325_);
return v___y_1324_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v___y_1324_);
v___x_1328_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__52);
lean_inc_ref(v_pos_1325_);
v___x_1329_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1328_, v___f_1122_, v_pos_1325_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_dec_ref(v_pos_1325_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_dec(v_idx_1326_);
return v___x_1329_;
}
else
{
lean_object* v_pos_1330_; lean_object* v_idx_1331_; 
v_pos_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_pos_1330_);
v_idx_1331_ = lean_ctor_get(v_pos_1330_, 1);
lean_inc(v_idx_1331_);
v_idx_1304_ = v_idx_1326_;
v___y_1305_ = v___x_1329_;
v_pos_1306_ = v_pos_1330_;
v_idx_1307_ = v_idx_1331_;
goto v___jp_1303_;
}
}
else
{
lean_object* v_err_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_err_1332_ = lean_ctor_get(v___x_1329_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; 
v_unused_1340_ = lean_ctor_get(v___x_1329_, 0);
lean_dec(v_unused_1340_);
v___x_1334_ = v___x_1329_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_err_1332_);
lean_dec(v___x_1329_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
lean_inc_ref(v_pos_1325_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v_pos_1325_);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_pos_1325_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_err_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_inc(v_idx_1326_);
v_idx_1304_ = v_idx_1326_;
v___y_1305_ = v___x_1337_;
v_pos_1306_ = v_pos_1325_;
v_idx_1307_ = v_idx_1326_;
goto v___jp_1303_;
}
}
}
}
}
v___jp_1342_:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_eq(v_idx_1343_, v_idx_1346_);
lean_dec(v_idx_1343_);
if (v___x_1347_ == 0)
{
lean_dec(v_idx_1346_);
lean_dec_ref(v_pos_1345_);
return v___y_1344_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec_ref(v___y_1344_);
v___x_1348_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__56);
lean_inc_ref(v_pos_1345_);
v___x_1349_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1348_, v___f_1341_, v_pos_1345_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_dec_ref(v_pos_1345_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_dec(v_idx_1346_);
return v___x_1349_;
}
else
{
lean_object* v_pos_1350_; lean_object* v_idx_1351_; 
v_pos_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_pos_1350_);
v_idx_1351_ = lean_ctor_get(v_pos_1350_, 1);
lean_inc(v_idx_1351_);
v_idx_1323_ = v_idx_1346_;
v___y_1324_ = v___x_1349_;
v_pos_1325_ = v_pos_1350_;
v_idx_1326_ = v_idx_1351_;
goto v___jp_1322_;
}
}
else
{
lean_object* v_err_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_err_1352_ = lean_ctor_get(v___x_1349_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v___x_1349_, 0);
lean_dec(v_unused_1360_);
v___x_1354_ = v___x_1349_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_err_1352_);
lean_dec(v___x_1349_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
lean_inc_ref(v_pos_1345_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_pos_1345_);
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_pos_1345_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_err_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_inc(v_idx_1346_);
v_idx_1323_ = v_idx_1346_;
v___y_1324_ = v___x_1357_;
v_pos_1325_ = v_pos_1345_;
v_idx_1326_ = v_idx_1346_;
goto v___jp_1322_;
}
}
}
}
}
v___jp_1361_:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_nat_dec_eq(v_idx_1362_, v_idx_1365_);
lean_dec(v_idx_1362_);
if (v___x_1366_ == 0)
{
lean_dec(v_idx_1365_);
lean_dec_ref(v_pos_1364_);
return v___y_1363_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v___y_1363_);
v___x_1367_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__59);
lean_inc_ref(v_pos_1364_);
v___x_1368_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1367_, v___f_1121_, v_pos_1364_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_dec_ref(v_pos_1364_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_dec(v_idx_1365_);
return v___x_1368_;
}
else
{
lean_object* v_pos_1369_; lean_object* v_idx_1370_; 
v_pos_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_pos_1369_);
v_idx_1370_ = lean_ctor_get(v_pos_1369_, 1);
lean_inc(v_idx_1370_);
v_idx_1343_ = v_idx_1365_;
v___y_1344_ = v___x_1368_;
v_pos_1345_ = v_pos_1369_;
v_idx_1346_ = v_idx_1370_;
goto v___jp_1342_;
}
}
else
{
lean_object* v_err_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_err_1371_ = lean_ctor_get(v___x_1368_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1368_, 0);
lean_dec(v_unused_1379_);
v___x_1373_ = v___x_1368_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_err_1371_);
lean_dec(v___x_1368_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
lean_inc_ref(v_pos_1364_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v_pos_1364_);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_pos_1364_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_err_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_inc(v_idx_1365_);
v_idx_1343_ = v_idx_1365_;
v___y_1344_ = v___x_1376_;
v_pos_1345_ = v_pos_1364_;
v_idx_1346_ = v_idx_1365_;
goto v___jp_1342_;
}
}
}
}
}
v___jp_1381_:
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_nat_dec_eq(v_idx_1382_, v_idx_1385_);
lean_dec(v_idx_1382_);
if (v___x_1386_ == 0)
{
lean_dec(v_idx_1385_);
lean_dec_ref(v_pos_1384_);
return v___y_1383_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec_ref(v___y_1383_);
v___x_1387_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__63);
lean_inc_ref(v_pos_1384_);
v___x_1388_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1387_, v___f_1380_, v_pos_1384_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_dec_ref(v_pos_1384_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_dec(v_idx_1385_);
return v___x_1388_;
}
else
{
lean_object* v_pos_1389_; lean_object* v_idx_1390_; 
v_pos_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_pos_1389_);
v_idx_1390_ = lean_ctor_get(v_pos_1389_, 1);
lean_inc(v_idx_1390_);
v_idx_1362_ = v_idx_1385_;
v___y_1363_ = v___x_1388_;
v_pos_1364_ = v_pos_1389_;
v_idx_1365_ = v_idx_1390_;
goto v___jp_1361_;
}
}
else
{
lean_object* v_err_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_err_1391_ = lean_ctor_get(v___x_1388_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1388_, 0);
lean_dec(v_unused_1399_);
v___x_1393_ = v___x_1388_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_err_1391_);
lean_dec(v___x_1388_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
lean_inc_ref(v_pos_1384_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_pos_1384_);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_pos_1384_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_err_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_inc(v_idx_1385_);
v_idx_1362_ = v_idx_1385_;
v___y_1363_ = v___x_1396_;
v_pos_1364_ = v_pos_1384_;
v_idx_1365_ = v_idx_1385_;
goto v___jp_1361_;
}
}
}
}
}
v___jp_1400_:
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_nat_dec_eq(v_idx_1401_, v_idx_1404_);
lean_dec(v_idx_1401_);
if (v___x_1405_ == 0)
{
lean_dec(v_idx_1404_);
lean_dec_ref(v_pos_1403_);
return v___y_1402_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v___y_1402_);
v___x_1406_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__66);
lean_inc_ref(v_pos_1403_);
v___x_1407_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1406_, v___f_1120_, v_pos_1403_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_dec_ref(v_pos_1403_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_dec(v_idx_1404_);
return v___x_1407_;
}
else
{
lean_object* v_pos_1408_; lean_object* v_idx_1409_; 
v_pos_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_pos_1408_);
v_idx_1409_ = lean_ctor_get(v_pos_1408_, 1);
lean_inc(v_idx_1409_);
v_idx_1382_ = v_idx_1404_;
v___y_1383_ = v___x_1407_;
v_pos_1384_ = v_pos_1408_;
v_idx_1385_ = v_idx_1409_;
goto v___jp_1381_;
}
}
else
{
lean_object* v_err_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_err_1410_ = lean_ctor_get(v___x_1407_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v___x_1407_, 0);
lean_dec(v_unused_1418_);
v___x_1412_ = v___x_1407_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_err_1410_);
lean_dec(v___x_1407_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
lean_inc_ref(v_pos_1403_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v_pos_1403_);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_pos_1403_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_err_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_inc(v_idx_1404_);
v_idx_1382_ = v_idx_1404_;
v___y_1383_ = v___x_1415_;
v_pos_1384_ = v_pos_1403_;
v_idx_1385_ = v_idx_1404_;
goto v___jp_1381_;
}
}
}
}
}
v___jp_1420_:
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_nat_dec_eq(v_idx_1421_, v_idx_1424_);
lean_dec(v_idx_1421_);
if (v___x_1425_ == 0)
{
lean_dec(v_idx_1424_);
lean_dec_ref(v_pos_1423_);
return v___y_1422_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v___y_1422_);
v___x_1426_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__70);
lean_inc_ref(v_pos_1423_);
v___x_1427_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1426_, v___f_1419_, v_pos_1423_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_dec_ref(v_pos_1423_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_dec(v_idx_1424_);
return v___x_1427_;
}
else
{
lean_object* v_pos_1428_; lean_object* v_idx_1429_; 
v_pos_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_pos_1428_);
v_idx_1429_ = lean_ctor_get(v_pos_1428_, 1);
lean_inc(v_idx_1429_);
v_idx_1401_ = v_idx_1424_;
v___y_1402_ = v___x_1427_;
v_pos_1403_ = v_pos_1428_;
v_idx_1404_ = v_idx_1429_;
goto v___jp_1400_;
}
}
else
{
lean_object* v_err_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_err_1430_ = lean_ctor_get(v___x_1427_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v___x_1427_, 0);
lean_dec(v_unused_1438_);
v___x_1432_ = v___x_1427_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_err_1430_);
lean_dec(v___x_1427_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
lean_inc_ref(v_pos_1423_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v_pos_1423_);
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_pos_1423_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_err_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_inc(v_idx_1424_);
v_idx_1401_ = v_idx_1424_;
v___y_1402_ = v___x_1435_;
v_pos_1403_ = v_pos_1423_;
v_idx_1404_ = v_idx_1424_;
goto v___jp_1400_;
}
}
}
}
}
v___jp_1439_:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_nat_dec_eq(v_idx_1440_, v_idx_1443_);
lean_dec(v_idx_1440_);
if (v___x_1444_ == 0)
{
lean_dec(v_idx_1443_);
lean_dec_ref(v_pos_1442_);
return v___y_1441_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v___y_1441_);
v___x_1445_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__73);
lean_inc_ref(v_pos_1442_);
v___x_1446_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1445_, v___f_1119_, v_pos_1442_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_dec_ref(v_pos_1442_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_dec(v_idx_1443_);
return v___x_1446_;
}
else
{
lean_object* v_pos_1447_; lean_object* v_idx_1448_; 
v_pos_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_pos_1447_);
v_idx_1448_ = lean_ctor_get(v_pos_1447_, 1);
lean_inc(v_idx_1448_);
v_idx_1421_ = v_idx_1443_;
v___y_1422_ = v___x_1446_;
v_pos_1423_ = v_pos_1447_;
v_idx_1424_ = v_idx_1448_;
goto v___jp_1420_;
}
}
else
{
lean_object* v_err_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
v_err_1449_ = lean_ctor_get(v___x_1446_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v___x_1446_, 0);
lean_dec(v_unused_1457_);
v___x_1451_ = v___x_1446_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_err_1449_);
lean_dec(v___x_1446_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
lean_inc_ref(v_pos_1442_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v_pos_1442_);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_pos_1442_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_err_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_inc(v_idx_1443_);
v_idx_1421_ = v_idx_1443_;
v___y_1422_ = v___x_1454_;
v_pos_1423_ = v_pos_1442_;
v_idx_1424_ = v_idx_1443_;
goto v___jp_1420_;
}
}
}
}
}
v___jp_1459_:
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_nat_dec_eq(v_idx_1460_, v_idx_1463_);
lean_dec(v_idx_1460_);
if (v___x_1464_ == 0)
{
lean_dec(v_idx_1463_);
lean_dec_ref(v_pos_1462_);
return v___y_1461_;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec_ref(v___y_1461_);
v___x_1465_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__77);
lean_inc_ref(v_pos_1462_);
v___x_1466_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1465_, v___f_1458_, v_pos_1462_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_dec_ref(v_pos_1462_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_dec(v_idx_1463_);
return v___x_1466_;
}
else
{
lean_object* v_pos_1467_; lean_object* v_idx_1468_; 
v_pos_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_pos_1467_);
v_idx_1468_ = lean_ctor_get(v_pos_1467_, 1);
lean_inc(v_idx_1468_);
v_idx_1440_ = v_idx_1463_;
v___y_1441_ = v___x_1466_;
v_pos_1442_ = v_pos_1467_;
v_idx_1443_ = v_idx_1468_;
goto v___jp_1439_;
}
}
else
{
lean_object* v_err_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_err_1469_ = lean_ctor_get(v___x_1466_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1466_, 0);
lean_dec(v_unused_1477_);
v___x_1471_ = v___x_1466_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_err_1469_);
lean_dec(v___x_1466_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
lean_inc_ref(v_pos_1462_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_pos_1462_);
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_pos_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_err_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_inc(v_idx_1463_);
v_idx_1440_ = v_idx_1463_;
v___y_1441_ = v___x_1474_;
v_pos_1442_ = v_pos_1462_;
v_idx_1443_ = v_idx_1463_;
goto v___jp_1439_;
}
}
}
}
}
v___jp_1478_:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_nat_dec_eq(v_idx_1479_, v_idx_1482_);
lean_dec(v_idx_1479_);
if (v___x_1483_ == 0)
{
lean_dec(v_idx_1482_);
lean_dec_ref(v_pos_1481_);
return v___y_1480_;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v___y_1480_);
v___x_1484_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__80);
lean_inc_ref(v_pos_1481_);
v___x_1485_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1484_, v___f_1118_, v_pos_1481_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref(v_pos_1481_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec(v_idx_1482_);
return v___x_1485_;
}
else
{
lean_object* v_pos_1486_; lean_object* v_idx_1487_; 
v_pos_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_pos_1486_);
v_idx_1487_ = lean_ctor_get(v_pos_1486_, 1);
lean_inc(v_idx_1487_);
v_idx_1460_ = v_idx_1482_;
v___y_1461_ = v___x_1485_;
v_pos_1462_ = v_pos_1486_;
v_idx_1463_ = v_idx_1487_;
goto v___jp_1459_;
}
}
else
{
lean_object* v_err_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
v_err_1488_ = lean_ctor_get(v___x_1485_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v___x_1485_, 0);
lean_dec(v_unused_1496_);
v___x_1490_ = v___x_1485_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_err_1488_);
lean_dec(v___x_1485_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
lean_inc_ref(v_pos_1481_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v_pos_1481_);
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_pos_1481_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_err_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_inc(v_idx_1482_);
v_idx_1460_ = v_idx_1482_;
v___y_1461_ = v___x_1493_;
v_pos_1462_ = v_pos_1481_;
v_idx_1463_ = v_idx_1482_;
goto v___jp_1459_;
}
}
}
}
}
v___jp_1498_:
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_nat_dec_eq(v_idx_1499_, v_idx_1502_);
lean_dec(v_idx_1499_);
if (v___x_1503_ == 0)
{
lean_dec(v_idx_1502_);
lean_dec_ref(v_pos_1501_);
return v___y_1500_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v___y_1500_);
v___x_1504_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__84);
lean_inc_ref(v_pos_1501_);
v___x_1505_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1504_, v___f_1497_, v_pos_1501_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_dec_ref(v_pos_1501_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_dec(v_idx_1502_);
return v___x_1505_;
}
else
{
lean_object* v_pos_1506_; lean_object* v_idx_1507_; 
v_pos_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_pos_1506_);
v_idx_1507_ = lean_ctor_get(v_pos_1506_, 1);
lean_inc(v_idx_1507_);
v_idx_1479_ = v_idx_1502_;
v___y_1480_ = v___x_1505_;
v_pos_1481_ = v_pos_1506_;
v_idx_1482_ = v_idx_1507_;
goto v___jp_1478_;
}
}
else
{
lean_object* v_err_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_err_1508_ = lean_ctor_get(v___x_1505_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v___x_1505_, 0);
lean_dec(v_unused_1516_);
v___x_1510_ = v___x_1505_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_err_1508_);
lean_dec(v___x_1505_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
lean_inc_ref(v_pos_1501_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v_pos_1501_);
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_pos_1501_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_err_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_inc(v_idx_1502_);
v_idx_1479_ = v_idx_1502_;
v___y_1480_ = v___x_1513_;
v_pos_1481_ = v_pos_1501_;
v_idx_1482_ = v_idx_1502_;
goto v___jp_1478_;
}
}
}
}
}
v___jp_1517_:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_nat_dec_eq(v_idx_1518_, v_idx_1521_);
lean_dec(v_idx_1518_);
if (v___x_1522_ == 0)
{
lean_dec(v_idx_1521_);
lean_dec_ref(v_pos_1520_);
return v___y_1519_;
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec_ref(v___y_1519_);
v___x_1523_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__87);
lean_inc_ref(v_pos_1520_);
v___x_1524_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1523_, v___f_1117_, v_pos_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_dec_ref(v_pos_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_dec(v_idx_1521_);
return v___x_1524_;
}
else
{
lean_object* v_pos_1525_; lean_object* v_idx_1526_; 
v_pos_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_pos_1525_);
v_idx_1526_ = lean_ctor_get(v_pos_1525_, 1);
lean_inc(v_idx_1526_);
v_idx_1499_ = v_idx_1521_;
v___y_1500_ = v___x_1524_;
v_pos_1501_ = v_pos_1525_;
v_idx_1502_ = v_idx_1526_;
goto v___jp_1498_;
}
}
else
{
lean_object* v_err_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
v_err_1527_ = lean_ctor_get(v___x_1524_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1524_, 0);
lean_dec(v_unused_1535_);
v___x_1529_ = v___x_1524_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_err_1527_);
lean_dec(v___x_1524_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
lean_inc_ref(v_pos_1520_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v_pos_1520_);
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_pos_1520_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_err_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_inc(v_idx_1521_);
v_idx_1499_ = v_idx_1521_;
v___y_1500_ = v___x_1532_;
v_pos_1501_ = v_pos_1520_;
v_idx_1502_ = v_idx_1521_;
goto v___jp_1498_;
}
}
}
}
}
v___jp_1537_:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_nat_dec_eq(v_idx_1538_, v_idx_1541_);
lean_dec(v_idx_1538_);
if (v___x_1542_ == 0)
{
lean_dec(v_idx_1541_);
lean_dec_ref(v_pos_1540_);
return v___y_1539_;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v___y_1539_);
v___x_1543_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__91);
lean_inc_ref(v_pos_1540_);
v___x_1544_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1543_, v___f_1536_, v_pos_1540_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_dec_ref(v_pos_1540_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_dec(v_idx_1541_);
return v___x_1544_;
}
else
{
lean_object* v_pos_1545_; lean_object* v_idx_1546_; 
v_pos_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_pos_1545_);
v_idx_1546_ = lean_ctor_get(v_pos_1545_, 1);
lean_inc(v_idx_1546_);
v_idx_1518_ = v_idx_1541_;
v___y_1519_ = v___x_1544_;
v_pos_1520_ = v_pos_1545_;
v_idx_1521_ = v_idx_1546_;
goto v___jp_1517_;
}
}
else
{
lean_object* v_err_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_err_1547_ = lean_ctor_get(v___x_1544_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v___x_1544_, 0);
lean_dec(v_unused_1555_);
v___x_1549_ = v___x_1544_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_err_1547_);
lean_dec(v___x_1544_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
lean_inc_ref(v_pos_1540_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_pos_1540_);
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_pos_1540_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_err_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_inc(v_idx_1541_);
v_idx_1518_ = v_idx_1541_;
v___y_1519_ = v___x_1552_;
v_pos_1520_ = v_pos_1540_;
v_idx_1521_ = v_idx_1541_;
goto v___jp_1517_;
}
}
}
}
}
v___jp_1556_:
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_nat_dec_eq(v_idx_1557_, v_idx_1560_);
lean_dec(v_idx_1557_);
if (v___x_1561_ == 0)
{
lean_dec(v_idx_1560_);
lean_dec_ref(v_pos_1559_);
return v___y_1558_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v___y_1558_);
v___x_1562_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__94);
lean_inc_ref(v_pos_1559_);
v___x_1563_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1562_, v___f_1116_, v_pos_1559_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_dec_ref(v_pos_1559_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_dec(v_idx_1560_);
return v___x_1563_;
}
else
{
lean_object* v_pos_1564_; lean_object* v_idx_1565_; 
v_pos_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_pos_1564_);
v_idx_1565_ = lean_ctor_get(v_pos_1564_, 1);
lean_inc(v_idx_1565_);
v_idx_1538_ = v_idx_1560_;
v___y_1539_ = v___x_1563_;
v_pos_1540_ = v_pos_1564_;
v_idx_1541_ = v_idx_1565_;
goto v___jp_1537_;
}
}
else
{
lean_object* v_err_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_err_1566_ = lean_ctor_get(v___x_1563_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v___x_1563_, 0);
lean_dec(v_unused_1574_);
v___x_1568_ = v___x_1563_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_err_1566_);
lean_dec(v___x_1563_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
lean_inc_ref(v_pos_1559_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_pos_1559_);
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_pos_1559_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_err_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_inc(v_idx_1560_);
v_idx_1538_ = v_idx_1560_;
v___y_1539_ = v___x_1571_;
v_pos_1540_ = v_pos_1559_;
v_idx_1541_ = v_idx_1560_;
goto v___jp_1537_;
}
}
}
}
}
v___jp_1576_:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_nat_dec_eq(v_idx_1577_, v_idx_1580_);
lean_dec(v_idx_1577_);
if (v___x_1581_ == 0)
{
lean_dec(v_idx_1580_);
lean_dec_ref(v_pos_1579_);
return v___y_1578_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v___y_1578_);
v___x_1582_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__98);
lean_inc_ref(v_pos_1579_);
v___x_1583_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1582_, v___f_1575_, v_pos_1579_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_dec_ref(v_pos_1579_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_dec(v_idx_1580_);
return v___x_1583_;
}
else
{
lean_object* v_pos_1584_; lean_object* v_idx_1585_; 
v_pos_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_pos_1584_);
v_idx_1585_ = lean_ctor_get(v_pos_1584_, 1);
lean_inc(v_idx_1585_);
v_idx_1557_ = v_idx_1580_;
v___y_1558_ = v___x_1583_;
v_pos_1559_ = v_pos_1584_;
v_idx_1560_ = v_idx_1585_;
goto v___jp_1556_;
}
}
else
{
lean_object* v_err_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_err_1586_ = lean_ctor_get(v___x_1583_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v___x_1583_, 0);
lean_dec(v_unused_1594_);
v___x_1588_ = v___x_1583_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_err_1586_);
lean_dec(v___x_1583_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
lean_inc_ref(v_pos_1579_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v_pos_1579_);
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_pos_1579_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_err_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_inc(v_idx_1580_);
v_idx_1557_ = v_idx_1580_;
v___y_1558_ = v___x_1591_;
v_pos_1559_ = v_pos_1579_;
v_idx_1560_ = v_idx_1580_;
goto v___jp_1556_;
}
}
}
}
}
v___jp_1595_:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_nat_dec_eq(v_idx_1596_, v_idx_1599_);
lean_dec(v_idx_1596_);
if (v___x_1600_ == 0)
{
lean_dec(v_idx_1599_);
lean_dec_ref(v_pos_1598_);
return v___y_1597_;
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v___y_1597_);
v___x_1601_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__101);
lean_inc_ref(v_pos_1598_);
v___x_1602_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1601_, v___f_1115_, v_pos_1598_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_dec_ref(v_pos_1598_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_dec(v_idx_1599_);
return v___x_1602_;
}
else
{
lean_object* v_pos_1603_; lean_object* v_idx_1604_; 
v_pos_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_pos_1603_);
v_idx_1604_ = lean_ctor_get(v_pos_1603_, 1);
lean_inc(v_idx_1604_);
v_idx_1577_ = v_idx_1599_;
v___y_1578_ = v___x_1602_;
v_pos_1579_ = v_pos_1603_;
v_idx_1580_ = v_idx_1604_;
goto v___jp_1576_;
}
}
else
{
lean_object* v_err_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_err_1605_ = lean_ctor_get(v___x_1602_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v___x_1602_, 0);
lean_dec(v_unused_1613_);
v___x_1607_ = v___x_1602_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_err_1605_);
lean_dec(v___x_1602_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
lean_inc_ref(v_pos_1598_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v_pos_1598_);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_pos_1598_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_err_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_inc(v_idx_1599_);
v_idx_1577_ = v_idx_1599_;
v___y_1578_ = v___x_1610_;
v_pos_1579_ = v_pos_1598_;
v_idx_1580_ = v_idx_1599_;
goto v___jp_1576_;
}
}
}
}
}
v___jp_1615_:
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_nat_dec_eq(v_idx_1616_, v_idx_1619_);
lean_dec(v_idx_1616_);
if (v___x_1620_ == 0)
{
lean_dec(v_idx_1619_);
lean_dec_ref(v_pos_1618_);
return v___y_1617_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v___y_1617_);
v___x_1621_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__105);
lean_inc_ref(v_pos_1618_);
v___x_1622_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1621_, v___f_1614_, v_pos_1618_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_dec_ref(v_pos_1618_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_dec(v_idx_1619_);
return v___x_1622_;
}
else
{
lean_object* v_pos_1623_; lean_object* v_idx_1624_; 
v_pos_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_pos_1623_);
v_idx_1624_ = lean_ctor_get(v_pos_1623_, 1);
lean_inc(v_idx_1624_);
v_idx_1596_ = v_idx_1619_;
v___y_1597_ = v___x_1622_;
v_pos_1598_ = v_pos_1623_;
v_idx_1599_ = v_idx_1624_;
goto v___jp_1595_;
}
}
else
{
lean_object* v_err_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v_err_1625_ = lean_ctor_get(v___x_1622_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v___x_1622_, 0);
lean_dec(v_unused_1633_);
v___x_1627_ = v___x_1622_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_err_1625_);
lean_dec(v___x_1622_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
lean_inc_ref(v_pos_1618_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v_pos_1618_);
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_pos_1618_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_err_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_inc(v_idx_1619_);
v_idx_1596_ = v_idx_1619_;
v___y_1597_ = v___x_1630_;
v_pos_1598_ = v_pos_1618_;
v_idx_1599_ = v_idx_1619_;
goto v___jp_1595_;
}
}
}
}
}
v___jp_1634_:
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_eq(v_idx_1635_, v_idx_1638_);
lean_dec(v_idx_1635_);
if (v___x_1639_ == 0)
{
lean_dec(v_idx_1638_);
lean_dec_ref(v_pos_1637_);
return v___y_1636_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v___y_1636_);
v___x_1640_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__108);
lean_inc_ref(v_pos_1637_);
v___x_1641_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1640_, v___f_1114_, v_pos_1637_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec_ref(v_pos_1637_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec(v_idx_1638_);
return v___x_1641_;
}
else
{
lean_object* v_pos_1642_; lean_object* v_idx_1643_; 
v_pos_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_pos_1642_);
v_idx_1643_ = lean_ctor_get(v_pos_1642_, 1);
lean_inc(v_idx_1643_);
v_idx_1616_ = v_idx_1638_;
v___y_1617_ = v___x_1641_;
v_pos_1618_ = v_pos_1642_;
v_idx_1619_ = v_idx_1643_;
goto v___jp_1615_;
}
}
else
{
lean_object* v_err_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_err_1644_ = lean_ctor_get(v___x_1641_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v___x_1641_, 0);
lean_dec(v_unused_1652_);
v___x_1646_ = v___x_1641_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_err_1644_);
lean_dec(v___x_1641_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
lean_inc_ref(v_pos_1637_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v_pos_1637_);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_pos_1637_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_err_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_inc(v_idx_1638_);
v_idx_1616_ = v_idx_1638_;
v___y_1617_ = v___x_1649_;
v_pos_1618_ = v_pos_1637_;
v_idx_1619_ = v_idx_1638_;
goto v___jp_1615_;
}
}
}
}
}
v___jp_1654_:
{
uint8_t v___x_1659_; 
v___x_1659_ = lean_nat_dec_eq(v_idx_1655_, v_idx_1658_);
lean_dec(v_idx_1655_);
if (v___x_1659_ == 0)
{
lean_dec(v_idx_1658_);
lean_dec_ref(v_pos_1657_);
return v___y_1656_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec_ref(v___y_1656_);
v___x_1660_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__112);
lean_inc_ref(v_pos_1657_);
v___x_1661_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1660_, v___f_1653_, v_pos_1657_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec_ref(v_pos_1657_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec(v_idx_1658_);
return v___x_1661_;
}
else
{
lean_object* v_pos_1662_; lean_object* v_idx_1663_; 
v_pos_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_pos_1662_);
v_idx_1663_ = lean_ctor_get(v_pos_1662_, 1);
lean_inc(v_idx_1663_);
v_idx_1635_ = v_idx_1658_;
v___y_1636_ = v___x_1661_;
v_pos_1637_ = v_pos_1662_;
v_idx_1638_ = v_idx_1663_;
goto v___jp_1634_;
}
}
else
{
lean_object* v_err_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_err_1664_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v___x_1661_, 0);
lean_dec(v_unused_1672_);
v___x_1666_ = v___x_1661_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_err_1664_);
lean_dec(v___x_1661_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
lean_inc_ref(v_pos_1657_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v_pos_1657_);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_pos_1657_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_err_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_inc(v_idx_1658_);
v_idx_1635_ = v_idx_1658_;
v___y_1636_ = v___x_1669_;
v_pos_1637_ = v_pos_1657_;
v_idx_1638_ = v_idx_1658_;
goto v___jp_1634_;
}
}
}
}
}
v___jp_1673_:
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_nat_dec_eq(v_idx_1674_, v_idx_1677_);
lean_dec(v_idx_1674_);
if (v___x_1678_ == 0)
{
lean_dec(v_idx_1677_);
lean_dec_ref(v_pos_1676_);
return v___y_1675_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v___y_1675_);
v___x_1679_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__115);
lean_inc_ref(v_pos_1676_);
v___x_1680_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1679_, v___f_1113_, v_pos_1676_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_dec_ref(v_pos_1676_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_dec(v_idx_1677_);
return v___x_1680_;
}
else
{
lean_object* v_pos_1681_; lean_object* v_idx_1682_; 
v_pos_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_pos_1681_);
v_idx_1682_ = lean_ctor_get(v_pos_1681_, 1);
lean_inc(v_idx_1682_);
v_idx_1655_ = v_idx_1677_;
v___y_1656_ = v___x_1680_;
v_pos_1657_ = v_pos_1681_;
v_idx_1658_ = v_idx_1682_;
goto v___jp_1654_;
}
}
else
{
lean_object* v_err_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_err_1683_ = lean_ctor_get(v___x_1680_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v___x_1680_, 0);
lean_dec(v_unused_1691_);
v___x_1685_ = v___x_1680_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_err_1683_);
lean_dec(v___x_1680_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
lean_inc_ref(v_pos_1676_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v_pos_1676_);
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_pos_1676_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_err_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_inc(v_idx_1677_);
v_idx_1655_ = v_idx_1677_;
v___y_1656_ = v___x_1688_;
v_pos_1657_ = v_pos_1676_;
v_idx_1658_ = v_idx_1677_;
goto v___jp_1654_;
}
}
}
}
}
v___jp_1693_:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_nat_dec_eq(v_idx_1694_, v_idx_1697_);
lean_dec(v_idx_1694_);
if (v___x_1698_ == 0)
{
lean_dec(v_idx_1697_);
lean_dec_ref(v_pos_1696_);
return v___y_1695_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec_ref(v___y_1695_);
v___x_1699_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__119);
lean_inc_ref(v_pos_1696_);
v___x_1700_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1699_, v___f_1692_, v_pos_1696_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_dec_ref(v_pos_1696_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_dec(v_idx_1697_);
return v___x_1700_;
}
else
{
lean_object* v_pos_1701_; lean_object* v_idx_1702_; 
v_pos_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_pos_1701_);
v_idx_1702_ = lean_ctor_get(v_pos_1701_, 1);
lean_inc(v_idx_1702_);
v_idx_1674_ = v_idx_1697_;
v___y_1675_ = v___x_1700_;
v_pos_1676_ = v_pos_1701_;
v_idx_1677_ = v_idx_1702_;
goto v___jp_1673_;
}
}
else
{
lean_object* v_err_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_err_1703_ = lean_ctor_get(v___x_1700_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1700_, 0);
lean_dec(v_unused_1711_);
v___x_1705_ = v___x_1700_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_err_1703_);
lean_dec(v___x_1700_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
lean_inc_ref(v_pos_1696_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v_pos_1696_);
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_pos_1696_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_err_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_inc(v_idx_1697_);
v_idx_1674_ = v_idx_1697_;
v___y_1675_ = v___x_1708_;
v_pos_1676_ = v_pos_1696_;
v_idx_1677_ = v_idx_1697_;
goto v___jp_1673_;
}
}
}
}
}
v___jp_1712_:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_nat_dec_eq(v_idx_1713_, v_idx_1716_);
lean_dec(v_idx_1713_);
if (v___x_1717_ == 0)
{
lean_dec(v_idx_1716_);
lean_dec_ref(v_pos_1715_);
return v___y_1714_;
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref(v___y_1714_);
v___x_1718_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__122);
lean_inc_ref(v_pos_1715_);
v___x_1719_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1718_, v___f_1112_, v_pos_1715_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_dec_ref(v_pos_1715_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_dec(v_idx_1716_);
return v___x_1719_;
}
else
{
lean_object* v_pos_1720_; lean_object* v_idx_1721_; 
v_pos_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_pos_1720_);
v_idx_1721_ = lean_ctor_get(v_pos_1720_, 1);
lean_inc(v_idx_1721_);
v_idx_1694_ = v_idx_1716_;
v___y_1695_ = v___x_1719_;
v_pos_1696_ = v_pos_1720_;
v_idx_1697_ = v_idx_1721_;
goto v___jp_1693_;
}
}
else
{
lean_object* v_err_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_err_1722_ = lean_ctor_get(v___x_1719_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1719_, 0);
lean_dec(v_unused_1730_);
v___x_1724_ = v___x_1719_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_err_1722_);
lean_dec(v___x_1719_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
lean_inc_ref(v_pos_1715_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v_pos_1715_);
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_pos_1715_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_err_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_inc(v_idx_1716_);
v_idx_1694_ = v_idx_1716_;
v___y_1695_ = v___x_1727_;
v_pos_1696_ = v_pos_1715_;
v_idx_1697_ = v_idx_1716_;
goto v___jp_1693_;
}
}
}
}
}
v___jp_1732_:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_nat_dec_eq(v_idx_1733_, v_idx_1736_);
lean_dec(v_idx_1733_);
if (v___x_1737_ == 0)
{
lean_dec(v_idx_1736_);
lean_dec_ref(v_pos_1735_);
return v___y_1734_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec_ref(v___y_1734_);
v___x_1738_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__126);
lean_inc_ref(v_pos_1735_);
v___x_1739_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1738_, v___f_1731_, v_pos_1735_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_dec_ref(v_pos_1735_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_dec(v_idx_1736_);
return v___x_1739_;
}
else
{
lean_object* v_pos_1740_; lean_object* v_idx_1741_; 
v_pos_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_pos_1740_);
v_idx_1741_ = lean_ctor_get(v_pos_1740_, 1);
lean_inc(v_idx_1741_);
v_idx_1713_ = v_idx_1736_;
v___y_1714_ = v___x_1739_;
v_pos_1715_ = v_pos_1740_;
v_idx_1716_ = v_idx_1741_;
goto v___jp_1712_;
}
}
else
{
lean_object* v_err_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_err_1742_ = lean_ctor_get(v___x_1739_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v___x_1739_, 0);
lean_dec(v_unused_1750_);
v___x_1744_ = v___x_1739_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_err_1742_);
lean_dec(v___x_1739_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
lean_inc_ref(v_pos_1735_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v_pos_1735_);
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_pos_1735_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_err_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_inc(v_idx_1736_);
v_idx_1713_ = v_idx_1736_;
v___y_1714_ = v___x_1747_;
v_pos_1715_ = v_pos_1735_;
v_idx_1716_ = v_idx_1736_;
goto v___jp_1712_;
}
}
}
}
}
v___jp_1751_:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_nat_dec_eq(v_idx_1752_, v_idx_1755_);
lean_dec(v_idx_1752_);
if (v___x_1756_ == 0)
{
lean_dec(v_idx_1755_);
lean_dec_ref(v_pos_1754_);
return v___y_1753_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec_ref(v___y_1753_);
v___x_1757_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__129);
lean_inc_ref(v_pos_1754_);
v___x_1758_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1757_, v___f_1111_, v_pos_1754_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_dec_ref(v_pos_1754_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_dec(v_idx_1755_);
return v___x_1758_;
}
else
{
lean_object* v_pos_1759_; lean_object* v_idx_1760_; 
v_pos_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_pos_1759_);
v_idx_1760_ = lean_ctor_get(v_pos_1759_, 1);
lean_inc(v_idx_1760_);
v_idx_1733_ = v_idx_1755_;
v___y_1734_ = v___x_1758_;
v_pos_1735_ = v_pos_1759_;
v_idx_1736_ = v_idx_1760_;
goto v___jp_1732_;
}
}
else
{
lean_object* v_err_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_err_1761_ = lean_ctor_get(v___x_1758_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1769_);
v___x_1763_ = v___x_1758_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_err_1761_);
lean_dec(v___x_1758_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
lean_inc_ref(v_pos_1754_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v_pos_1754_);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_pos_1754_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_err_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_inc(v_idx_1755_);
v_idx_1733_ = v_idx_1755_;
v___y_1734_ = v___x_1766_;
v_pos_1735_ = v_pos_1754_;
v_idx_1736_ = v_idx_1755_;
goto v___jp_1732_;
}
}
}
}
}
v___jp_1771_:
{
uint8_t v___x_1776_; 
v___x_1776_ = lean_nat_dec_eq(v_idx_1772_, v_idx_1775_);
lean_dec(v_idx_1772_);
if (v___x_1776_ == 0)
{
lean_dec(v_idx_1775_);
lean_dec_ref(v_pos_1774_);
return v___y_1773_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec_ref(v___y_1773_);
v___x_1777_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__133);
lean_inc_ref(v_pos_1774_);
v___x_1778_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1777_, v___f_1770_, v_pos_1774_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_dec_ref(v_pos_1774_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_dec(v_idx_1775_);
return v___x_1778_;
}
else
{
lean_object* v_pos_1779_; lean_object* v_idx_1780_; 
v_pos_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_pos_1779_);
v_idx_1780_ = lean_ctor_get(v_pos_1779_, 1);
lean_inc(v_idx_1780_);
v_idx_1752_ = v_idx_1775_;
v___y_1753_ = v___x_1778_;
v_pos_1754_ = v_pos_1779_;
v_idx_1755_ = v_idx_1780_;
goto v___jp_1751_;
}
}
else
{
lean_object* v_err_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_err_1781_ = lean_ctor_get(v___x_1778_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v___x_1778_, 0);
lean_dec(v_unused_1789_);
v___x_1783_ = v___x_1778_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_err_1781_);
lean_dec(v___x_1778_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
lean_inc_ref(v_pos_1774_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v_pos_1774_);
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_pos_1774_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_err_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_inc(v_idx_1775_);
v_idx_1752_ = v_idx_1775_;
v___y_1753_ = v___x_1786_;
v_pos_1754_ = v_pos_1774_;
v_idx_1755_ = v_idx_1775_;
goto v___jp_1751_;
}
}
}
}
}
v___jp_1790_:
{
uint8_t v___x_1795_; 
v___x_1795_ = lean_nat_dec_eq(v_idx_1791_, v_idx_1794_);
lean_dec(v_idx_1791_);
if (v___x_1795_ == 0)
{
lean_dec(v_idx_1794_);
lean_dec_ref(v_pos_1793_);
return v___y_1792_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec_ref(v___y_1792_);
v___x_1796_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__136);
lean_inc_ref(v_pos_1793_);
v___x_1797_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1796_, v___f_1110_, v_pos_1793_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec_ref(v_pos_1793_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec(v_idx_1794_);
return v___x_1797_;
}
else
{
lean_object* v_pos_1798_; lean_object* v_idx_1799_; 
v_pos_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_pos_1798_);
v_idx_1799_ = lean_ctor_get(v_pos_1798_, 1);
lean_inc(v_idx_1799_);
v_idx_1772_ = v_idx_1794_;
v___y_1773_ = v___x_1797_;
v_pos_1774_ = v_pos_1798_;
v_idx_1775_ = v_idx_1799_;
goto v___jp_1771_;
}
}
else
{
lean_object* v_err_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_err_1800_ = lean_ctor_get(v___x_1797_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1807_ == 0)
{
lean_object* v_unused_1808_; 
v_unused_1808_ = lean_ctor_get(v___x_1797_, 0);
lean_dec(v_unused_1808_);
v___x_1802_ = v___x_1797_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_err_1800_);
lean_dec(v___x_1797_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
lean_inc_ref(v_pos_1793_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v_pos_1793_);
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_pos_1793_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_err_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_inc(v_idx_1794_);
v_idx_1772_ = v_idx_1794_;
v___y_1773_ = v___x_1805_;
v_pos_1774_ = v_pos_1793_;
v_idx_1775_ = v_idx_1794_;
goto v___jp_1771_;
}
}
}
}
}
v___jp_1810_:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_nat_dec_eq(v_idx_1811_, v_idx_1814_);
lean_dec(v_idx_1811_);
if (v___x_1815_ == 0)
{
lean_dec(v_idx_1814_);
lean_dec_ref(v_pos_1813_);
return v___y_1812_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec_ref(v___y_1812_);
v___x_1816_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__140);
lean_inc_ref(v_pos_1813_);
v___x_1817_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1816_, v___f_1809_, v_pos_1813_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_dec_ref(v_pos_1813_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_dec(v_idx_1814_);
return v___x_1817_;
}
else
{
lean_object* v_pos_1818_; lean_object* v_idx_1819_; 
v_pos_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_pos_1818_);
v_idx_1819_ = lean_ctor_get(v_pos_1818_, 1);
lean_inc(v_idx_1819_);
v_idx_1791_ = v_idx_1814_;
v___y_1792_ = v___x_1817_;
v_pos_1793_ = v_pos_1818_;
v_idx_1794_ = v_idx_1819_;
goto v___jp_1790_;
}
}
else
{
lean_object* v_err_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_err_1820_ = lean_ctor_get(v___x_1817_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v___x_1817_, 0);
lean_dec(v_unused_1828_);
v___x_1822_ = v___x_1817_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_err_1820_);
lean_dec(v___x_1817_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
lean_inc_ref(v_pos_1813_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v_pos_1813_);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_pos_1813_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_err_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_inc(v_idx_1814_);
v_idx_1791_ = v_idx_1814_;
v___y_1792_ = v___x_1825_;
v_pos_1793_ = v_pos_1813_;
v_idx_1794_ = v_idx_1814_;
goto v___jp_1790_;
}
}
}
}
}
v___jp_1829_:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_nat_dec_eq(v_idx_1830_, v_idx_1833_);
lean_dec(v_idx_1830_);
if (v___x_1834_ == 0)
{
lean_dec(v_idx_1833_);
lean_dec_ref(v_pos_1832_);
return v___y_1831_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v___y_1831_);
v___x_1835_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__143);
lean_inc_ref(v_pos_1832_);
v___x_1836_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1835_, v___f_1109_, v_pos_1832_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_dec_ref(v_pos_1832_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_dec(v_idx_1833_);
return v___x_1836_;
}
else
{
lean_object* v_pos_1837_; lean_object* v_idx_1838_; 
v_pos_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_pos_1837_);
v_idx_1838_ = lean_ctor_get(v_pos_1837_, 1);
lean_inc(v_idx_1838_);
v_idx_1811_ = v_idx_1833_;
v___y_1812_ = v___x_1836_;
v_pos_1813_ = v_pos_1837_;
v_idx_1814_ = v_idx_1838_;
goto v___jp_1810_;
}
}
else
{
lean_object* v_err_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_err_1839_ = lean_ctor_get(v___x_1836_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v___x_1836_, 0);
lean_dec(v_unused_1847_);
v___x_1841_ = v___x_1836_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_err_1839_);
lean_dec(v___x_1836_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
lean_inc_ref(v_pos_1832_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v_pos_1832_);
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_pos_1832_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_err_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_inc(v_idx_1833_);
v_idx_1811_ = v_idx_1833_;
v___y_1812_ = v___x_1844_;
v_pos_1813_ = v_pos_1832_;
v_idx_1814_ = v_idx_1833_;
goto v___jp_1810_;
}
}
}
}
}
v___jp_1849_:
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_nat_dec_eq(v_idx_1850_, v_idx_1853_);
lean_dec(v_idx_1850_);
if (v___x_1854_ == 0)
{
lean_dec(v_idx_1853_);
lean_dec_ref(v_pos_1852_);
return v___y_1851_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec_ref(v___y_1851_);
v___x_1855_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__147);
lean_inc_ref(v_pos_1852_);
v___x_1856_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1855_, v___f_1848_, v_pos_1852_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_dec_ref(v_pos_1852_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_dec(v_idx_1853_);
return v___x_1856_;
}
else
{
lean_object* v_pos_1857_; lean_object* v_idx_1858_; 
v_pos_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_pos_1857_);
v_idx_1858_ = lean_ctor_get(v_pos_1857_, 1);
lean_inc(v_idx_1858_);
v_idx_1830_ = v_idx_1853_;
v___y_1831_ = v___x_1856_;
v_pos_1832_ = v_pos_1857_;
v_idx_1833_ = v_idx_1858_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_err_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_err_1859_ = lean_ctor_get(v___x_1856_, 1);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v___x_1856_, 0);
lean_dec(v_unused_1867_);
v___x_1861_ = v___x_1856_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_err_1859_);
lean_dec(v___x_1856_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
lean_inc_ref(v_pos_1852_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v_pos_1852_);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_pos_1852_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_err_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_inc(v_idx_1853_);
v_idx_1830_ = v_idx_1853_;
v___y_1831_ = v___x_1864_;
v_pos_1832_ = v_pos_1852_;
v_idx_1833_ = v_idx_1853_;
goto v___jp_1829_;
}
}
}
}
}
v___jp_1868_:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_nat_dec_eq(v_idx_1869_, v_idx_1872_);
lean_dec(v_idx_1869_);
if (v___x_1873_ == 0)
{
lean_dec(v_idx_1872_);
lean_dec_ref(v_pos_1871_);
return v___y_1870_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v___y_1870_);
v___x_1874_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__150);
lean_inc_ref(v_pos_1871_);
v___x_1875_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1874_, v___f_1108_, v_pos_1871_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_dec_ref(v_pos_1871_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_dec(v_idx_1872_);
return v___x_1875_;
}
else
{
lean_object* v_pos_1876_; lean_object* v_idx_1877_; 
v_pos_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_pos_1876_);
v_idx_1877_ = lean_ctor_get(v_pos_1876_, 1);
lean_inc(v_idx_1877_);
v_idx_1850_ = v_idx_1872_;
v___y_1851_ = v___x_1875_;
v_pos_1852_ = v_pos_1876_;
v_idx_1853_ = v_idx_1877_;
goto v___jp_1849_;
}
}
else
{
lean_object* v_err_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
v_err_1878_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v___x_1875_, 0);
lean_dec(v_unused_1886_);
v___x_1880_ = v___x_1875_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_err_1878_);
lean_dec(v___x_1875_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
lean_inc_ref(v_pos_1871_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_pos_1871_);
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_pos_1871_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_err_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_inc(v_idx_1872_);
v_idx_1850_ = v_idx_1872_;
v___y_1851_ = v___x_1883_;
v_pos_1852_ = v_pos_1871_;
v_idx_1853_ = v_idx_1872_;
goto v___jp_1849_;
}
}
}
}
}
v___jp_1888_:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_nat_dec_eq(v_idx_1889_, v_idx_1892_);
lean_dec(v_idx_1889_);
if (v___x_1893_ == 0)
{
lean_dec(v_idx_1892_);
lean_dec_ref(v_pos_1891_);
return v___y_1890_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec_ref(v___y_1890_);
v___x_1894_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__154);
lean_inc_ref(v_pos_1891_);
v___x_1895_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1894_, v___f_1887_, v_pos_1891_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_dec_ref(v_pos_1891_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_dec(v_idx_1892_);
return v___x_1895_;
}
else
{
lean_object* v_pos_1896_; lean_object* v_idx_1897_; 
v_pos_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_pos_1896_);
v_idx_1897_ = lean_ctor_get(v_pos_1896_, 1);
lean_inc(v_idx_1897_);
v_idx_1869_ = v_idx_1892_;
v___y_1870_ = v___x_1895_;
v_pos_1871_ = v_pos_1896_;
v_idx_1872_ = v_idx_1897_;
goto v___jp_1868_;
}
}
else
{
lean_object* v_err_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_err_1898_ = lean_ctor_get(v___x_1895_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v___x_1895_, 0);
lean_dec(v_unused_1906_);
v___x_1900_ = v___x_1895_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_err_1898_);
lean_dec(v___x_1895_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
lean_inc_ref(v_pos_1891_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v_pos_1891_);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_pos_1891_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_err_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_inc(v_idx_1892_);
v_idx_1869_ = v_idx_1892_;
v___y_1870_ = v___x_1903_;
v_pos_1871_ = v_pos_1891_;
v_idx_1872_ = v_idx_1892_;
goto v___jp_1868_;
}
}
}
}
}
v___jp_1907_:
{
lean_object* v_idx_1910_; lean_object* v_idx_1911_; uint8_t v___x_1912_; 
v_idx_1910_ = lean_ctor_get(v_a_1106_, 1);
lean_inc(v_idx_1910_);
lean_dec_ref(v_a_1106_);
v_idx_1911_ = lean_ctor_get(v_pos_1909_, 1);
lean_inc(v_idx_1911_);
v___x_1912_ = lean_nat_dec_eq(v_idx_1910_, v_idx_1911_);
lean_dec(v_idx_1910_);
if (v___x_1912_ == 0)
{
lean_dec(v_idx_1911_);
lean_dec_ref(v_pos_1909_);
return v___y_1908_;
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec_ref(v___y_1908_);
v___x_1913_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod___closed__157);
lean_inc_ref(v_pos_1909_);
v___x_1914_ = l_Functor_mapRev___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod_spec__0___redArg(v___x_1913_, v___f_1107_, v_pos_1909_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_dec_ref(v_pos_1909_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_dec(v_idx_1911_);
return v___x_1914_;
}
else
{
lean_object* v_pos_1915_; lean_object* v_idx_1916_; 
v_pos_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_pos_1915_);
v_idx_1916_ = lean_ctor_get(v_pos_1915_, 1);
lean_inc(v_idx_1916_);
v_idx_1889_ = v_idx_1911_;
v___y_1890_ = v___x_1914_;
v_pos_1891_ = v_pos_1915_;
v_idx_1892_ = v_idx_1916_;
goto v___jp_1888_;
}
}
else
{
lean_object* v_err_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_err_1917_ = lean_ctor_get(v___x_1914_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v___x_1914_, 0);
lean_dec(v_unused_1925_);
v___x_1919_ = v___x_1914_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_err_1917_);
lean_dec(v___x_1914_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
lean_inc_ref(v_pos_1909_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v_pos_1909_);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_pos_1909_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_err_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_inc(v_idx_1911_);
v_idx_1889_ = v_idx_1911_;
v___y_1890_ = v___x_1922_;
v_pos_1891_ = v_pos_1909_;
v_idx_1892_ = v_idx_1911_;
goto v___jp_1888_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(uint8_t v_b_1939_){
_start:
{
uint8_t v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = 32;
v___x_1941_ = lean_uint8_dec_eq(v_b_1939_, v___x_1940_);
if (v___x_1941_ == 0)
{
uint8_t v___x_1942_; 
v___x_1942_ = 1;
return v___x_1942_;
}
else
{
uint8_t v___x_1943_; 
v___x_1943_ = 0;
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0___boxed(lean_object* v_b_1944_){
_start:
{
uint8_t v_b_boxed_1945_; uint8_t v_res_1946_; lean_object* v_r_1947_; 
v_b_boxed_1945_ = lean_unbox(v_b_1944_);
v_res_1946_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___lam__0(v_b_boxed_1945_);
v_r_1947_ = lean_box(v_res_1946_);
return v_r_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(lean_object* v_limits_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v_maxUriLength_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_snd_1963_; lean_object* v_snd_1964_; uint8_t v___x_1965_; 
v_maxUriLength_1959_ = lean_ctor_get(v_limits_1952_, 4);
v___f_1960_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__0));
v___x_1961_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1953_);
v___x_1962_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_1960_, v_maxUriLength_1959_, v___x_1961_, v_a_1953_);
v_snd_1963_ = lean_ctor_get(v___x_1962_, 1);
lean_inc(v_snd_1963_);
v_snd_1964_ = lean_ctor_get(v_snd_1963_, 1);
v___x_1965_ = lean_unbox(v_snd_1964_);
if (v___x_1965_ == 0)
{
lean_object* v_fst_1966_; lean_object* v_fst_1967_; lean_object* v_array_1968_; lean_object* v_idx_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1996_; 
v_fst_1966_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_fst_1966_);
lean_dec_ref(v___x_1962_);
v_fst_1967_ = lean_ctor_get(v_snd_1963_, 0);
lean_inc(v_fst_1967_);
lean_dec(v_snd_1963_);
v_array_1968_ = lean_ctor_get(v_a_1953_, 0);
v_idx_1969_ = lean_ctor_get(v_a_1953_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_a_1953_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1971_ = v_a_1953_;
v_isShared_1972_ = v_isSharedCheck_1996_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_idx_1969_);
lean_inc(v_array_1968_);
lean_dec(v_a_1953_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1996_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_lower_1974_; lean_object* v_upper_1975_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___y_1993_; uint8_t v___x_1995_; 
v___x_1990_ = lean_nat_add(v_idx_1969_, v_fst_1966_);
lean_dec(v_fst_1966_);
v___x_1991_ = lean_byte_array_size(v_array_1968_);
v___x_1995_ = lean_nat_dec_le(v_idx_1969_, v___x_1961_);
if (v___x_1995_ == 0)
{
v___y_1993_ = v_idx_1969_;
goto v___jp_1992_;
}
else
{
lean_dec(v_idx_1969_);
v___y_1993_ = v___x_1961_;
goto v___jp_1992_;
}
v___jp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = l_ByteArray_toByteSlice(v_array_1968_, v_lower_1974_, v_upper_1975_);
v___x_1977_ = l_ByteSlice_size(v___x_1976_);
v___x_1978_ = lean_nat_dec_eq(v___x_1977_, v_maxUriLength_1959_);
lean_dec(v___x_1977_);
if (v___x_1978_ == 0)
{
lean_del_object(v___x_1971_);
v___y_1955_ = v___x_1976_;
v___y_1956_ = v_fst_1967_;
goto v___jp_1954_;
}
else
{
lean_object* v_array_1979_; lean_object* v_idx_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_array_1979_ = lean_ctor_get(v_fst_1967_, 0);
v_idx_1980_ = lean_ctor_get(v_fst_1967_, 1);
v___x_1981_ = lean_byte_array_size(v_array_1979_);
v___x_1982_ = lean_nat_dec_lt(v_idx_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_del_object(v___x_1971_);
v___y_1955_ = v___x_1976_;
v___y_1956_ = v_fst_1967_;
goto v___jp_1954_;
}
else
{
uint8_t v___x_1983_; uint8_t v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = lean_byte_array_fget(v_array_1979_, v_idx_1980_);
v___x_1984_ = 32;
v___x_1985_ = lean_uint8_dec_eq(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_dec_ref(v___x_1976_);
v___x_1986_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___closed__2));
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 1);
lean_ctor_set(v___x_1971_, 1, v___x_1986_);
lean_ctor_set(v___x_1971_, 0, v_fst_1967_);
v___x_1988_ = v___x_1971_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_fst_1967_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_del_object(v___x_1971_);
v___y_1955_ = v___x_1976_;
v___y_1956_ = v_fst_1967_;
goto v___jp_1954_;
}
}
}
}
v___jp_1992_:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_nat_dec_le(v___x_1990_, v___x_1991_);
if (v___x_1994_ == 0)
{
lean_dec(v___x_1990_);
v_lower_1974_ = v___y_1993_;
v_upper_1975_ = v___x_1991_;
goto v___jp_1973_;
}
else
{
v_lower_1974_ = v___y_1993_;
v_upper_1975_ = v___x_1990_;
goto v___jp_1973_;
}
}
}
}
else
{
lean_object* v_fst_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref(v___x_1962_);
lean_dec_ref(v_a_1953_);
v_fst_1997_ = lean_ctor_get(v_snd_1963_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_snd_1963_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v_snd_1963_, 1);
lean_dec(v_unused_2006_);
v___x_1999_ = v_snd_1963_;
v_isShared_2000_ = v_isSharedCheck_2005_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_fst_1997_);
lean_dec(v_snd_1963_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2005_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_2001_ = lean_box(0);
if (v_isShared_2000_ == 0)
{
lean_ctor_set_tag(v___x_1999_, 1);
lean_ctor_set(v___x_1999_, 1, v___x_2001_);
v___x_2003_ = v___x_1999_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_fst_1997_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
v___jp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = l_ByteSlice_toByteArray(v___y_1955_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___y_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI___boxed(lean_object* v_limits_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2007_, v_a_2008_);
lean_dec_ref(v_limits_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0(lean_object* v___x_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_2013_, v___y_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_pos_2016_; lean_object* v_array_2017_; lean_object* v_idx_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_pos_2016_ = lean_ctor_get(v___x_2015_, 0);
v_array_2017_ = lean_ctor_get(v_pos_2016_, 0);
v_idx_2018_ = lean_ctor_get(v_pos_2016_, 1);
v___x_2019_ = lean_byte_array_size(v_array_2017_);
v___x_2020_ = lean_nat_dec_lt(v_idx_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
return v___x_2015_;
}
else
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
lean_inc(v_pos_2016_);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; lean_object* v_unused_2030_; 
v_unused_2029_ = lean_ctor_get(v___x_2015_, 1);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2030_);
v___x_2022_ = v___x_2015_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v___x_2015_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___lam__0___closed__1));
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 1);
lean_ctor_set(v___x_2022_, 1, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_pos_2016_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2024_);
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
else
{
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(lean_object* v_limits_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___y_2044_; lean_object* v_pos_2045_; lean_object* v_res_2046_; lean_object* v_pos_2050_; lean_object* v_res_2051_; lean_object* v___x_2090_; 
v___x_2090_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseURI(v_limits_2041_, v_a_2042_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_pos_2091_; lean_object* v_res_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2122_; 
v_pos_2091_ = lean_ctor_get(v___x_2090_, 0);
v_res_2092_ = lean_ctor_get(v___x_2090_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2094_ = v___x_2090_;
v_isShared_2095_ = v_isSharedCheck_2122_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_res_2092_);
lean_inc(v_pos_2091_);
lean_dec(v___x_2090_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2122_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_array_2096_; lean_object* v_idx_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_array_2096_ = lean_ctor_get(v_pos_2091_, 0);
v_idx_2097_ = lean_ctor_get(v_pos_2091_, 1);
v___x_2098_ = lean_byte_array_size(v_array_2096_);
v___x_2099_ = lean_nat_dec_lt(v_idx_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec(v_res_2092_);
v___x_2100_ = lean_box(0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 1);
lean_ctor_set(v___x_2094_, 1, v___x_2100_);
v___x_2102_ = v___x_2094_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_pos_2091_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
uint8_t v___x_2104_; uint8_t v_got_2105_; uint8_t v___x_2106_; 
v___x_2104_ = 32;
v_got_2105_ = lean_byte_array_fget(v_array_2096_, v_idx_2097_);
v___x_2106_ = lean_uint8_dec_eq(v_got_2105_, v___x_2104_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec(v_res_2092_);
v___x_2107_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 1);
lean_ctor_set(v___x_2094_, 1, v___x_2107_);
v___x_2109_ = v___x_2094_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_pos_2091_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
else
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2119_; 
lean_inc(v_idx_2097_);
lean_inc_ref(v_array_2096_);
lean_del_object(v___x_2094_);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_pos_2091_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; lean_object* v_unused_2121_; 
v_unused_2120_ = lean_ctor_get(v_pos_2091_, 1);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_pos_2091_, 0);
lean_dec(v_unused_2121_);
v___x_2112_ = v_pos_2091_;
v_isShared_2113_ = v_isSharedCheck_2119_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v_pos_2091_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2119_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = lean_nat_add(v_idx_2097_, v___x_2114_);
lean_dec(v_idx_2097_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___x_2115_);
v___x_2117_ = v___x_2112_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_array_2096_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
v_pos_2050_ = v___x_2117_;
v_res_2051_ = v_res_2092_;
goto v___jp_2049_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_pos_2123_; lean_object* v_res_2124_; 
v_pos_2123_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_pos_2123_);
v_res_2124_ = lean_ctor_get(v___x_2090_, 1);
lean_inc(v_res_2124_);
lean_dec_ref_known(v___x_2090_, 2);
v_pos_2050_ = v_pos_2123_;
v_res_2051_ = v_res_2124_;
goto v___jp_2049_;
}
else
{
lean_object* v_pos_2125_; lean_object* v_err_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_pos_2125_ = lean_ctor_get(v___x_2090_, 0);
v_err_2126_ = lean_ctor_get(v___x_2090_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2090_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_err_2126_);
lean_inc(v_pos_2125_);
lean_dec(v___x_2090_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_pos_2125_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_err_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
v___jp_2043_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___y_2044_);
lean_ctor_set(v___x_2047_, 1, v_res_2046_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v_pos_2045_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
return v___x_2048_;
}
v___jp_2049_:
{
lean_object* v___f_2052_; lean_object* v___x_2053_; 
v___f_2052_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___closed__1));
v___x_2053_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_2052_, v_res_2051_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2062_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 1);
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2060_, 0, v_pos_2050_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
return v___x_2060_;
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2064_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_pos_2050_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_pos_2065_; lean_object* v_res_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_pos_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_pos_2065_);
v_res_2066_ = lean_ctor_get(v___x_2064_, 1);
lean_inc(v_res_2066_);
lean_dec_ref_known(v___x_2064_, 2);
v___x_2067_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2068_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2067_, v_pos_2065_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_pos_2069_; 
v_pos_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_pos_2069_);
lean_dec_ref_known(v___x_2068_, 2);
v___y_2044_ = v_a_2063_;
v_pos_2045_ = v_pos_2069_;
v_res_2046_ = v_res_2066_;
goto v___jp_2043_;
}
else
{
lean_object* v_pos_2070_; lean_object* v_err_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_res_2066_);
lean_dec(v_a_2063_);
v_pos_2070_ = lean_ctor_get(v___x_2068_, 0);
v_err_2071_ = lean_ctor_get(v___x_2068_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2068_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_err_2071_);
lean_inc(v_pos_2070_);
lean_dec(v___x_2068_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_pos_2070_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_err_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_pos_2079_; lean_object* v_res_2080_; 
v_pos_2079_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_pos_2079_);
v_res_2080_ = lean_ctor_get(v___x_2064_, 1);
lean_inc(v_res_2080_);
lean_dec_ref_known(v___x_2064_, 2);
v___y_2044_ = v_a_2063_;
v_pos_2045_ = v_pos_2079_;
v_res_2046_ = v_res_2080_;
goto v___jp_2043_;
}
else
{
lean_object* v_pos_2081_; lean_object* v_err_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_2063_);
v_pos_2081_ = lean_ctor_get(v___x_2064_, 0);
v_err_2082_ = lean_ctor_get(v___x_2064_, 1);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2064_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_err_2082_);
lean_inc(v_pos_2081_);
lean_dec(v___x_2064_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_pos_2081_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_err_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody___boxed(lean_object* v_limits_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2134_, v_a_2135_);
lean_dec_ref(v_limits_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine(lean_object* v_limits_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___y_2143_; uint8_t v___y_2147_; uint8_t v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v_pos_2159_; uint8_t v_res_2160_; lean_object* v___x_2191_; 
v___x_2191_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_pos_2192_; lean_object* v___x_2193_; 
v_pos_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_pos_2192_);
lean_dec_ref_known(v___x_2191_, 2);
v___x_2193_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2192_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_pos_2194_; lean_object* v_res_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2226_; 
v_pos_2194_ = lean_ctor_get(v___x_2193_, 0);
v_res_2195_ = lean_ctor_get(v___x_2193_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2197_ = v___x_2193_;
v_isShared_2198_ = v_isSharedCheck_2226_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_res_2195_);
lean_inc(v_pos_2194_);
lean_dec(v___x_2193_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2226_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v_array_2199_; lean_object* v_idx_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v_array_2199_ = lean_ctor_get(v_pos_2194_, 0);
v_idx_2200_ = lean_ctor_get(v_pos_2194_, 1);
v___x_2201_ = lean_byte_array_size(v_array_2199_);
v___x_2202_ = lean_nat_dec_lt(v_idx_2200_, v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
lean_dec(v_res_2195_);
v___x_2203_ = lean_box(0);
if (v_isShared_2198_ == 0)
{
lean_ctor_set_tag(v___x_2197_, 1);
lean_ctor_set(v___x_2197_, 1, v___x_2203_);
v___x_2205_ = v___x_2197_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_pos_2194_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
else
{
uint8_t v___x_2207_; uint8_t v_got_2208_; uint8_t v___x_2209_; 
v___x_2207_ = 32;
v_got_2208_ = lean_byte_array_fget(v_array_2199_, v_idx_2200_);
v___x_2209_ = lean_uint8_dec_eq(v_got_2208_, v___x_2207_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
lean_dec(v_res_2195_);
v___x_2210_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2198_ == 0)
{
lean_ctor_set_tag(v___x_2197_, 1);
lean_ctor_set(v___x_2197_, 1, v___x_2210_);
v___x_2212_ = v___x_2197_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_pos_2194_);
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
lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2223_; 
lean_inc(v_idx_2200_);
lean_inc_ref(v_array_2199_);
lean_del_object(v___x_2197_);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_pos_2194_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; lean_object* v_unused_2225_; 
v_unused_2224_ = lean_ctor_get(v_pos_2194_, 1);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v_pos_2194_, 0);
lean_dec(v_unused_2225_);
v___x_2215_ = v_pos_2194_;
v_isShared_2216_ = v_isSharedCheck_2223_;
goto v_resetjp_2214_;
}
else
{
lean_dec(v_pos_2194_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2223_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2217_ = lean_unsigned_to_nat(1u);
v___x_2218_ = lean_nat_add(v_idx_2200_, v___x_2217_);
lean_dec(v_idx_2200_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v___x_2218_);
v___x_2220_ = v___x_2215_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_array_2199_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
uint8_t v___x_2221_; 
v___x_2221_ = lean_unbox(v_res_2195_);
lean_dec(v_res_2195_);
v_pos_2159_ = v___x_2220_;
v_res_2160_ = v___x_2221_;
goto v___jp_2158_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_pos_2227_; lean_object* v_res_2228_; uint8_t v___x_2229_; 
v_pos_2227_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_pos_2227_);
v_res_2228_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_res_2228_);
lean_dec_ref_known(v___x_2193_, 2);
v___x_2229_ = lean_unbox(v_res_2228_);
lean_dec(v_res_2228_);
v_pos_2159_ = v_pos_2227_;
v_res_2160_ = v___x_2229_;
goto v___jp_2158_;
}
else
{
lean_object* v_pos_2230_; lean_object* v_err_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
v_pos_2230_ = lean_ctor_get(v___x_2193_, 0);
v_err_2231_ = lean_ctor_get(v___x_2193_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2193_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_err_2231_);
lean_inc(v_pos_2230_);
lean_dec(v___x_2193_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_pos_2230_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_err_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
else
{
lean_object* v_pos_2239_; lean_object* v_err_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
v_pos_2239_ = lean_ctor_get(v___x_2191_, 0);
v_err_2240_ = lean_ctor_get(v___x_2191_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2191_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_err_2240_);
lean_inc(v_pos_2239_);
lean_dec(v___x_2191_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_pos_2239_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_err_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
v___jp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___y_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
return v___x_2145_;
}
v___jp_2146_:
{
if (v___y_2148_ == 0)
{
lean_dec(v___y_2151_);
lean_dec(v___y_2149_);
v___y_2143_ = v___y_2150_;
goto v___jp_2142_;
}
else
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = lean_unsigned_to_nat(0u);
v___x_2153_ = lean_nat_dec_eq(v___y_2149_, v___x_2152_);
lean_dec(v___y_2149_);
if (v___x_2153_ == 0)
{
lean_dec(v___y_2151_);
v___y_2143_ = v___y_2150_;
goto v___jp_2142_;
}
else
{
uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2154_ = 0;
v___x_2155_ = l_Std_Http_Headers_empty;
v___x_2156_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2156_, 0, v___y_2151_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2, v___y_2147_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2 + 1, v___x_2154_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___y_2150_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
return v___x_2157_;
}
}
}
v___jp_2158_:
{
lean_object* v___x_2161_; 
v___x_2161_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2140_, v_pos_2159_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_res_2162_; lean_object* v_snd_2163_; lean_object* v_pos_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2180_; 
v_res_2162_ = lean_ctor_get(v___x_2161_, 1);
lean_inc(v_res_2162_);
v_snd_2163_ = lean_ctor_get(v_res_2162_, 1);
lean_inc(v_snd_2163_);
v_pos_2164_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v___x_2161_, 1);
lean_dec(v_unused_2181_);
v___x_2166_ = v___x_2161_;
v_isShared_2167_ = v_isSharedCheck_2180_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_pos_2164_);
lean_dec(v___x_2161_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2180_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_fst_2168_; lean_object* v_fst_2169_; lean_object* v_snd_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v_fst_2168_ = lean_ctor_get(v_res_2162_, 0);
lean_inc(v_fst_2168_);
lean_dec(v_res_2162_);
v_fst_2169_ = lean_ctor_get(v_snd_2163_, 0);
lean_inc(v_fst_2169_);
v_snd_2170_ = lean_ctor_get(v_snd_2163_, 1);
lean_inc(v_snd_2170_);
lean_dec(v_snd_2163_);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_dec_eq(v_fst_2169_, v___x_2171_);
lean_dec(v_fst_2169_);
if (v___x_2172_ == 0)
{
lean_del_object(v___x_2166_);
v___y_2147_ = v_res_2160_;
v___y_2148_ = v___x_2172_;
v___y_2149_ = v_snd_2170_;
v___y_2150_ = v_pos_2164_;
v___y_2151_ = v_fst_2168_;
goto v___jp_2146_;
}
else
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_nat_dec_eq(v_snd_2170_, v___x_2171_);
if (v___x_2173_ == 0)
{
lean_del_object(v___x_2166_);
v___y_2147_ = v_res_2160_;
v___y_2148_ = v___x_2172_;
v___y_2149_ = v_snd_2170_;
v___y_2150_ = v_pos_2164_;
v___y_2151_ = v_fst_2168_;
goto v___jp_2146_;
}
else
{
uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_dec(v_snd_2170_);
v___x_2174_ = 1;
v___x_2175_ = l_Std_Http_Headers_empty;
v___x_2176_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_2176_, 0, v_fst_2168_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*2, v_res_2160_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*2 + 1, v___x_2174_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v___x_2176_);
v___x_2178_ = v___x_2166_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_pos_2164_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
else
{
lean_object* v_pos_2182_; lean_object* v_err_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
v_pos_2182_ = lean_ctor_get(v___x_2161_, 0);
v_err_2183_ = lean_ctor_get(v___x_2161_, 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2161_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_err_2183_);
lean_inc(v_pos_2182_);
lean_dec(v___x_2161_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_pos_2182_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_err_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLine___boxed(lean_object* v_limits_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_Http_Protocol_H1_parseRequestLine(v_limits_2248_, v_a_2249_);
lean_dec_ref(v_limits_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion(lean_object* v_limits_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_pos_2254_; uint8_t v_res_2255_; lean_object* v___x_2297_; 
v___x_2297_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_skipLeadingRequestEmptyLines(v_limits_2251_, v_a_2252_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_pos_2298_; lean_object* v___x_2299_; 
v_pos_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_pos_2298_);
lean_dec_ref_known(v___x_2297_, 2);
v___x_2299_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseMethod(v_pos_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_pos_2300_; lean_object* v_res_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2332_; 
v_pos_2300_ = lean_ctor_get(v___x_2299_, 0);
v_res_2301_ = lean_ctor_get(v___x_2299_, 1);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2303_ = v___x_2299_;
v_isShared_2304_ = v_isSharedCheck_2332_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_res_2301_);
lean_inc(v_pos_2300_);
lean_dec(v___x_2299_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2332_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_array_2305_; lean_object* v_idx_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_array_2305_ = lean_ctor_get(v_pos_2300_, 0);
v_idx_2306_ = lean_ctor_get(v_pos_2300_, 1);
v___x_2307_ = lean_byte_array_size(v_array_2305_);
v___x_2308_ = lean_nat_dec_lt(v_idx_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
lean_dec(v_res_2301_);
v___x_2309_ = lean_box(0);
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 1);
lean_ctor_set(v___x_2303_, 1, v___x_2309_);
v___x_2311_ = v___x_2303_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_pos_2300_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
else
{
uint8_t v___x_2313_; uint8_t v_got_2314_; uint8_t v___x_2315_; 
v___x_2313_ = 32;
v_got_2314_ = lean_byte_array_fget(v_array_2305_, v_idx_2306_);
v___x_2315_ = lean_uint8_dec_eq(v_got_2314_, v___x_2313_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_dec(v_res_2301_);
v___x_2316_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_2304_ == 0)
{
lean_ctor_set_tag(v___x_2303_, 1);
lean_ctor_set(v___x_2303_, 1, v___x_2316_);
v___x_2318_ = v___x_2303_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_pos_2300_);
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
lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2329_; 
lean_inc(v_idx_2306_);
lean_inc_ref(v_array_2305_);
lean_del_object(v___x_2303_);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_pos_2300_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; lean_object* v_unused_2331_; 
v_unused_2330_ = lean_ctor_get(v_pos_2300_, 1);
lean_dec(v_unused_2330_);
v_unused_2331_ = lean_ctor_get(v_pos_2300_, 0);
lean_dec(v_unused_2331_);
v___x_2321_ = v_pos_2300_;
v_isShared_2322_ = v_isSharedCheck_2329_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v_pos_2300_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2329_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2323_ = lean_unsigned_to_nat(1u);
v___x_2324_ = lean_nat_add(v_idx_2306_, v___x_2323_);
lean_dec(v_idx_2306_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v___x_2324_);
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_array_2305_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_unbox(v_res_2301_);
lean_dec(v_res_2301_);
v_pos_2254_ = v___x_2326_;
v_res_2255_ = v___x_2327_;
goto v___jp_2253_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_pos_2333_; lean_object* v_res_2334_; uint8_t v___x_2335_; 
v_pos_2333_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_pos_2333_);
v_res_2334_ = lean_ctor_get(v___x_2299_, 1);
lean_inc(v_res_2334_);
lean_dec_ref_known(v___x_2299_, 2);
v___x_2335_ = lean_unbox(v_res_2334_);
lean_dec(v_res_2334_);
v_pos_2254_ = v_pos_2333_;
v_res_2255_ = v___x_2335_;
goto v___jp_2253_;
}
else
{
lean_object* v_pos_2336_; lean_object* v_err_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v_pos_2336_ = lean_ctor_get(v___x_2299_, 0);
v_err_2337_ = lean_ctor_get(v___x_2299_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2299_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_err_2337_);
lean_inc(v_pos_2336_);
lean_dec(v___x_2299_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_pos_2336_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_err_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
else
{
lean_object* v_pos_2345_; lean_object* v_err_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
v_pos_2345_ = lean_ctor_get(v___x_2297_, 0);
v_err_2346_ = lean_ctor_get(v___x_2297_, 1);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2297_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_err_2346_);
lean_inc(v_pos_2345_);
lean_dec(v___x_2297_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_pos_2345_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_err_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
v___jp_2253_:
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseRequestLineBody(v_limits_2251_, v_pos_2254_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_res_2257_; lean_object* v_snd_2258_; lean_object* v_pos_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2286_; 
v_res_2257_ = lean_ctor_get(v___x_2256_, 1);
lean_inc(v_res_2257_);
v_snd_2258_ = lean_ctor_get(v_res_2257_, 1);
lean_inc(v_snd_2258_);
v_pos_2259_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; 
v_unused_2287_ = lean_ctor_get(v___x_2256_, 1);
lean_dec(v_unused_2287_);
v___x_2261_ = v___x_2256_;
v_isShared_2262_ = v_isSharedCheck_2286_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_pos_2259_);
lean_dec(v___x_2256_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2286_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v_fst_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2284_; 
v_fst_2263_ = lean_ctor_get(v_res_2257_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_res_2257_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v_res_2257_, 1);
lean_dec(v_unused_2285_);
v___x_2265_ = v_res_2257_;
v_isShared_2266_ = v_isSharedCheck_2284_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_fst_2263_);
lean_dec(v_res_2257_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2284_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v_fst_2267_; lean_object* v_snd_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2283_; 
v_fst_2267_ = lean_ctor_get(v_snd_2258_, 0);
v_snd_2268_ = lean_ctor_get(v_snd_2258_, 1);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_snd_2258_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2270_ = v_snd_2258_;
v_isShared_2271_ = v_isSharedCheck_2283_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_snd_2268_);
lean_inc(v_fst_2267_);
lean_dec(v_snd_2258_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2283_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = l_Std_Http_Version_ofNumber_x3f(v_fst_2267_, v_snd_2268_);
lean_dec(v_snd_2268_);
lean_dec(v_fst_2267_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v___x_2272_);
lean_ctor_set(v___x_2270_, 0, v_fst_2263_);
v___x_2274_ = v___x_2270_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_fst_2263_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = lean_box(v_res_2255_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 1, v___x_2274_);
lean_ctor_set(v___x_2265_, 0, v___x_2275_);
v___x_2277_ = v___x_2265_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2274_);
v___x_2277_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___x_2277_);
v___x_2279_ = v___x_2261_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_pos_2259_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2288_; lean_object* v_err_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_pos_2288_ = lean_ctor_get(v___x_2256_, 0);
v_err_2289_ = lean_ctor_get(v___x_2256_, 1);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2256_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_err_2289_);
lean_inc(v_pos_2288_);
lean_dec(v___x_2256_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_pos_2288_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_err_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseRequestLineRawVersion___boxed(lean_object* v_limits_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Std_Http_Protocol_H1_parseRequestLineRawVersion(v_limits_2354_, v_a_2355_);
lean_dec_ref(v_limits_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(uint8_t v___y_2357_){
_start:
{
uint32_t v___x_2358_; uint32_t v___x_2359_; uint8_t v___x_2360_; 
v___x_2358_ = lean_uint8_to_uint32(v___y_2357_);
v___x_2359_ = 32;
v___x_2360_ = lean_uint32_dec_eq(v___x_2358_, v___x_2359_);
if (v___x_2360_ == 0)
{
uint32_t v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = 9;
v___x_2362_ = lean_uint32_dec_eq(v___x_2358_, v___x_2361_);
return v___x_2362_;
}
else
{
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1___boxed(lean_object* v___y_2363_){
_start:
{
uint8_t v___y_3721__boxed_2364_; uint8_t v_res_2365_; lean_object* v_r_2366_; 
v___y_3721__boxed_2364_ = lean_unbox(v___y_2363_);
v_res_2365_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__1(v___y_3721__boxed_2364_);
v_r_2366_ = lean_box(v_res_2365_);
return v_r_2366_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(uint8_t v___y_2367_){
_start:
{
uint32_t v___x_2368_; uint32_t v___x_2374_; uint8_t v___x_2375_; 
v___x_2368_ = lean_uint8_to_uint32(v___y_2367_);
v___x_2374_ = 33;
v___x_2375_ = lean_uint32_dec_le(v___x_2374_, v___x_2368_);
if (v___x_2375_ == 0)
{
goto v___jp_2369_;
}
else
{
uint32_t v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = 126;
v___x_2377_ = lean_uint32_dec_le(v___x_2368_, v___x_2376_);
if (v___x_2377_ == 0)
{
goto v___jp_2369_;
}
else
{
return v___x_2377_;
}
}
v___jp_2369_:
{
uint32_t v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = 32;
v___x_2371_ = lean_uint32_dec_eq(v___x_2368_, v___x_2370_);
if (v___x_2371_ == 0)
{
uint32_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = 9;
v___x_2373_ = lean_uint32_dec_eq(v___x_2368_, v___x_2372_);
return v___x_2373_;
}
else
{
return v___x_2371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2___boxed(lean_object* v___y_2378_){
_start:
{
uint8_t v___y_3734__boxed_2379_; uint8_t v_res_2380_; lean_object* v_r_2381_; 
v___y_3734__boxed_2379_ = lean_unbox(v___y_2378_);
v_res_2380_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___lam__2(v___y_3734__boxed_2379_);
v_r_2381_ = lean_box(v_res_2380_);
return v_r_2381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(lean_object* v_s_2382_, lean_object* v_pos_2383_){
_start:
{
lean_object* v_str_2384_; lean_object* v_startInclusive_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v_decide_2389_; 
v_str_2384_ = lean_ctor_get(v_s_2382_, 0);
v_startInclusive_2385_ = lean_ctor_get(v_s_2382_, 1);
v___x_2386_ = lean_nat_add(v_startInclusive_2385_, v_pos_2383_);
v___x_2387_ = lean_nat_sub(v___x_2386_, v_startInclusive_2385_);
v___x_2388_ = lean_unsigned_to_nat(0u);
v_decide_2389_ = lean_nat_dec_eq(v___x_2387_, v___x_2388_);
if (v_decide_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2398_; uint32_t v___x_2399_; uint32_t v___x_2400_; uint8_t v___x_2401_; 
lean_inc(v_startInclusive_2385_);
lean_inc_ref(v_str_2384_);
v___x_2390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2390_, 0, v_str_2384_);
lean_ctor_set(v___x_2390_, 1, v_startInclusive_2385_);
lean_ctor_set(v___x_2390_, 2, v___x_2386_);
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = lean_nat_sub(v___x_2387_, v___x_2391_);
lean_dec(v___x_2387_);
v___x_2393_ = l_String_Slice_posLE(v___x_2390_, v___x_2392_);
lean_dec_ref_known(v___x_2390_, 3);
v___x_2398_ = lean_nat_add(v_startInclusive_2385_, v___x_2393_);
v___x_2399_ = lean_string_utf8_get_fast(v_str_2384_, v___x_2398_);
lean_dec(v___x_2398_);
v___x_2400_ = 32;
v___x_2401_ = lean_uint32_dec_eq(v___x_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
uint32_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = 9;
v___x_2403_ = lean_uint32_dec_eq(v___x_2399_, v___x_2402_);
if (v___x_2403_ == 0)
{
uint32_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = 13;
v___x_2405_ = lean_uint32_dec_eq(v___x_2399_, v___x_2404_);
if (v___x_2405_ == 0)
{
uint32_t v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = 10;
v___x_2407_ = lean_uint32_dec_eq(v___x_2399_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_dec(v___x_2393_);
return v_pos_2383_;
}
else
{
goto v___jp_2394_;
}
}
else
{
goto v___jp_2394_;
}
}
else
{
goto v___jp_2394_;
}
}
else
{
goto v___jp_2394_;
}
v___jp_2394_:
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = lean_nat_add(v___x_2393_, v___x_2391_);
v___x_2396_ = lean_nat_dec_le(v___x_2395_, v_pos_2383_);
lean_dec(v___x_2395_);
if (v___x_2396_ == 0)
{
lean_dec(v___x_2393_);
return v_pos_2383_;
}
else
{
lean_dec(v_pos_2383_);
v_pos_2383_ = v___x_2393_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2387_);
lean_dec(v___x_2386_);
return v_pos_2383_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0___boxed(lean_object* v_s_2408_, lean_object* v_pos_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v_s_2408_, v_pos_2409_);
lean_dec_ref(v_s_2408_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(lean_object* v_limits_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_pos_2419_; lean_object* v_pos_2423_; lean_object* v_maxHeaderNameLength_2426_; lean_object* v_maxHeaderValueLength_2427_; lean_object* v_maxSpaceSequence_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2490_; lean_object* v_pos_2491_; lean_object* v_res_2492_; lean_object* v___x_2498_; lean_object* v_snd_2499_; lean_object* v_snd_2500_; uint8_t v___x_2501_; 
v_maxHeaderNameLength_2426_ = lean_ctor_get(v_limits_2416_, 6);
v_maxHeaderValueLength_2427_ = lean_ctor_get(v_limits_2416_, 7);
v_maxSpaceSequence_2428_ = lean_ctor_get(v_limits_2416_, 8);
v___f_2429_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_2430_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2417_);
v___x_2498_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2429_, v_maxHeaderNameLength_2426_, v___x_2430_, v_a_2417_);
v_snd_2499_ = lean_ctor_get(v___x_2498_, 1);
lean_inc(v_snd_2499_);
v_snd_2500_ = lean_ctor_get(v_snd_2499_, 1);
v___x_2501_ = lean_unbox(v_snd_2500_);
if (v___x_2501_ == 0)
{
lean_object* v_fst_2502_; lean_object* v_fst_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2661_; 
v_fst_2502_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_fst_2502_);
lean_dec_ref(v___x_2498_);
v_fst_2503_ = lean_ctor_get(v_snd_2499_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_snd_2499_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; 
v_unused_2662_ = lean_ctor_get(v_snd_2499_, 1);
lean_dec(v_unused_2662_);
v___x_2505_ = v_snd_2499_;
v_isShared_2506_ = v_isSharedCheck_2661_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_fst_2503_);
lean_dec(v_snd_2499_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2661_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_nat_dec_eq(v_fst_2502_, v___x_2430_);
if (v___x_2507_ == 0)
{
lean_object* v_array_2508_; lean_object* v_idx_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2656_; 
v_array_2508_ = lean_ctor_get(v_a_2417_, 0);
v_idx_2509_ = lean_ctor_get(v_a_2417_, 1);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_a_2417_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2511_ = v_a_2417_;
v_isShared_2512_ = v_isSharedCheck_2656_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_idx_2509_);
lean_inc(v_array_2508_);
lean_dec(v_a_2417_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2656_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___f_2513_; lean_object* v___y_2515_; lean_object* v_pos_2516_; lean_object* v_res_2517_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v_lower_2547_; lean_object* v_upper_2548_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___f_2559_; lean_object* v___y_2561_; lean_object* v_pos_2562_; lean_object* v___y_2589_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___y_2647_; uint8_t v___x_2655_; 
v___f_2513_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___f_2559_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_2644_ = lean_nat_add(v_idx_2509_, v_fst_2502_);
lean_dec(v_fst_2502_);
v___x_2645_ = lean_byte_array_size(v_array_2508_);
v___x_2655_ = lean_nat_dec_le(v_idx_2509_, v___x_2430_);
if (v___x_2655_ == 0)
{
v___y_2647_ = v_idx_2509_;
goto v___jp_2646_;
}
else
{
lean_dec(v_idx_2509_);
v___y_2647_ = v___x_2430_;
goto v___jp_2646_;
}
v___jp_2514_:
{
lean_object* v___x_2518_; lean_object* v_snd_2519_; lean_object* v_snd_2520_; uint8_t v___x_2521_; 
v___x_2518_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2513_, v_maxSpaceSequence_2428_, v___x_2430_, v_pos_2516_);
v_snd_2519_ = lean_ctor_get(v___x_2518_, 1);
lean_inc(v_snd_2519_);
lean_dec_ref(v___x_2518_);
v_snd_2520_ = lean_ctor_get(v_snd_2519_, 1);
v___x_2521_ = lean_unbox(v_snd_2520_);
if (v___x_2521_ == 0)
{
lean_object* v_fst_2522_; lean_object* v_array_2523_; lean_object* v_idx_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_fst_2522_ = lean_ctor_get(v_snd_2519_, 0);
lean_inc(v_fst_2522_);
lean_dec(v_snd_2519_);
v_array_2523_ = lean_ctor_get(v_fst_2522_, 0);
v_idx_2524_ = lean_ctor_get(v_fst_2522_, 1);
v___x_2525_ = lean_byte_array_size(v_array_2523_);
v___x_2526_ = lean_nat_dec_lt(v_idx_2524_, v___x_2525_);
if (v___x_2526_ == 0)
{
v___y_2490_ = v___y_2515_;
v_pos_2491_ = v_fst_2522_;
v_res_2492_ = v_res_2517_;
goto v___jp_2489_;
}
else
{
uint8_t v___x_2527_; uint32_t v___x_2528_; uint32_t v___x_2529_; uint8_t v___x_2530_; 
v___x_2527_ = lean_byte_array_fget(v_array_2523_, v_idx_2524_);
v___x_2528_ = lean_uint8_to_uint32(v___x_2527_);
v___x_2529_ = 32;
v___x_2530_ = lean_uint32_dec_eq(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
uint32_t v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = 9;
v___x_2532_ = lean_uint32_dec_eq(v___x_2528_, v___x_2531_);
if (v___x_2532_ == 0)
{
v___y_2490_ = v___y_2515_;
v_pos_2491_ = v_fst_2522_;
v_res_2492_ = v_res_2517_;
goto v___jp_2489_;
}
else
{
lean_dec(v_res_2517_);
lean_dec_ref(v___y_2515_);
v_pos_2423_ = v_fst_2522_;
goto v___jp_2422_;
}
}
else
{
lean_dec(v_res_2517_);
lean_dec_ref(v___y_2515_);
v_pos_2423_ = v_fst_2522_;
goto v___jp_2422_;
}
}
}
else
{
lean_object* v_fst_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_res_2517_);
lean_dec_ref(v___y_2515_);
v_fst_2533_ = lean_ctor_get(v_snd_2519_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_snd_2519_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v_snd_2519_, 1);
lean_dec(v_unused_2542_);
v___x_2535_ = v_snd_2519_;
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_fst_2533_);
lean_dec(v_snd_2519_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2537_ = lean_box(0);
if (v_isShared_2536_ == 0)
{
lean_ctor_set_tag(v___x_2535_, 1);
lean_ctor_set(v___x_2535_, 1, v___x_2537_);
v___x_2539_ = v___x_2535_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_fst_2533_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
v___jp_2543_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = l_ByteArray_toByteSlice(v___y_2545_, v_lower_2547_, v_upper_2548_);
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
v___y_2515_ = v___y_2544_;
v_pos_2516_ = v___y_2546_;
v_res_2517_ = v___x_2550_;
goto v___jp_2514_;
}
v___jp_2551_:
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_nat_dec_le(v___y_2556_, v___y_2552_);
if (v___x_2558_ == 0)
{
lean_dec(v___y_2556_);
v___y_2544_ = v___y_2553_;
v___y_2545_ = v___y_2554_;
v___y_2546_ = v___y_2555_;
v_lower_2547_ = v___y_2557_;
v_upper_2548_ = v___y_2552_;
goto v___jp_2543_;
}
else
{
lean_dec(v___y_2552_);
v___y_2544_ = v___y_2553_;
v___y_2545_ = v___y_2554_;
v___y_2546_ = v___y_2555_;
v_lower_2547_ = v___y_2557_;
v_upper_2548_ = v___y_2556_;
goto v___jp_2543_;
}
}
v___jp_2560_:
{
lean_object* v___x_2563_; lean_object* v_snd_2564_; lean_object* v_snd_2565_; uint8_t v___x_2566_; 
lean_inc_ref(v_pos_2562_);
v___x_2563_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2559_, v_maxHeaderValueLength_2427_, v___x_2430_, v_pos_2562_);
v_snd_2564_ = lean_ctor_get(v___x_2563_, 1);
lean_inc(v_snd_2564_);
v_snd_2565_ = lean_ctor_get(v_snd_2564_, 1);
v___x_2566_ = lean_unbox(v_snd_2565_);
if (v___x_2566_ == 0)
{
lean_object* v_fst_2567_; lean_object* v_fst_2568_; lean_object* v_array_2569_; lean_object* v_idx_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_fst_2567_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_fst_2567_);
lean_dec_ref(v___x_2563_);
v_fst_2568_ = lean_ctor_get(v_snd_2564_, 0);
lean_inc(v_fst_2568_);
lean_dec(v_snd_2564_);
v_array_2569_ = lean_ctor_get(v_pos_2562_, 0);
lean_inc_ref(v_array_2569_);
v_idx_2570_ = lean_ctor_get(v_pos_2562_, 1);
lean_inc(v_idx_2570_);
lean_dec_ref(v_pos_2562_);
v___x_2571_ = lean_nat_add(v_idx_2570_, v_fst_2567_);
lean_dec(v_fst_2567_);
v___x_2572_ = lean_byte_array_size(v_array_2569_);
v___x_2573_ = lean_nat_dec_le(v_idx_2570_, v___x_2430_);
if (v___x_2573_ == 0)
{
v___y_2552_ = v___x_2572_;
v___y_2553_ = v___y_2561_;
v___y_2554_ = v_array_2569_;
v___y_2555_ = v_fst_2568_;
v___y_2556_ = v___x_2571_;
v___y_2557_ = v_idx_2570_;
goto v___jp_2551_;
}
else
{
lean_dec(v_idx_2570_);
v___y_2552_ = v___x_2572_;
v___y_2553_ = v___y_2561_;
v___y_2554_ = v_array_2569_;
v___y_2555_ = v_fst_2568_;
v___y_2556_ = v___x_2571_;
v___y_2557_ = v___x_2430_;
goto v___jp_2551_;
}
}
else
{
lean_object* v_fst_2574_; lean_object* v_idx_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref(v___x_2563_);
v_fst_2574_ = lean_ctor_get(v_snd_2564_, 0);
lean_inc(v_fst_2574_);
lean_dec(v_snd_2564_);
v_idx_2575_ = lean_ctor_get(v_pos_2562_, 1);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_pos_2562_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v_pos_2562_, 0);
lean_dec(v_unused_2587_);
v___x_2577_ = v_pos_2562_;
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_idx_2575_);
lean_dec(v_pos_2562_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_idx_2579_; uint8_t v___x_2580_; 
v_idx_2579_ = lean_ctor_get(v_fst_2574_, 1);
v___x_2580_ = lean_nat_dec_eq(v_idx_2575_, v_idx_2579_);
lean_dec(v_idx_2575_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
lean_dec_ref(v___y_2561_);
v___x_2581_ = lean_box(0);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 1, v___x_2581_);
lean_ctor_set(v___x_2577_, 0, v_fst_2574_);
v___x_2583_ = v___x_2577_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_fst_2574_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
else
{
lean_object* v___x_2585_; 
lean_del_object(v___x_2577_);
v___x_2585_ = lean_box(0);
v___y_2515_ = v___y_2561_;
v_pos_2516_ = v_fst_2574_;
v_res_2517_ = v___x_2585_;
goto v___jp_2514_;
}
}
}
}
v___jp_2588_:
{
lean_object* v_array_2590_; lean_object* v_idx_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_array_2590_ = lean_ctor_get(v_fst_2503_, 0);
v_idx_2591_ = lean_ctor_get(v_fst_2503_, 1);
v___x_2592_ = lean_byte_array_size(v_array_2590_);
v___x_2593_ = lean_nat_dec_lt(v_idx_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_dec_ref(v___y_2589_);
lean_dec_ref(v_array_2508_);
v___x_2594_ = lean_box(0);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 1);
lean_ctor_set(v___x_2511_, 1, v___x_2594_);
lean_ctor_set(v___x_2511_, 0, v_fst_2503_);
v___x_2596_ = v___x_2511_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_fst_2503_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
else
{
uint8_t v___x_2598_; uint8_t v_got_2599_; uint8_t v___x_2600_; 
v___x_2598_ = 58;
v_got_2599_ = lean_byte_array_fget(v_array_2590_, v_idx_2591_);
v___x_2600_ = lean_uint8_dec_eq(v_got_2599_, v___x_2598_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2603_; 
lean_dec_ref(v___y_2589_);
lean_dec_ref(v_array_2508_);
v___x_2601_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__3));
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 1);
lean_ctor_set(v___x_2511_, 1, v___x_2601_);
lean_ctor_set(v___x_2511_, 0, v_fst_2503_);
v___x_2603_ = v___x_2511_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_fst_2503_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2641_; 
lean_inc(v_idx_2591_);
lean_inc_ref(v_array_2590_);
lean_del_object(v___x_2511_);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_fst_2503_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; lean_object* v_unused_2643_; 
v_unused_2642_ = lean_ctor_get(v_fst_2503_, 1);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_fst_2503_, 0);
lean_dec(v_unused_2643_);
v___x_2606_ = v_fst_2503_;
v_isShared_2607_ = v_isSharedCheck_2641_;
goto v_resetjp_2605_;
}
else
{
lean_dec(v_fst_2503_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2641_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2608_ = lean_unsigned_to_nat(1u);
v___x_2609_ = lean_nat_add(v_idx_2591_, v___x_2608_);
lean_dec(v_idx_2591_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v___x_2609_);
v___x_2611_ = v___x_2606_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_array_2590_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; lean_object* v_snd_2613_; lean_object* v_snd_2614_; uint8_t v___x_2615_; 
v___x_2612_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2513_, v_maxSpaceSequence_2428_, v___x_2430_, v___x_2611_);
v_snd_2613_ = lean_ctor_get(v___x_2612_, 1);
lean_inc(v_snd_2613_);
lean_dec_ref(v___x_2612_);
v_snd_2614_ = lean_ctor_get(v_snd_2613_, 1);
v___x_2615_ = lean_unbox(v_snd_2614_);
if (v___x_2615_ == 0)
{
lean_object* v_fst_2616_; lean_object* v_array_2617_; lean_object* v_idx_2618_; lean_object* v_lower_2619_; lean_object* v_upper_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_fst_2616_ = lean_ctor_get(v_snd_2613_, 0);
lean_inc(v_fst_2616_);
lean_dec(v_snd_2613_);
v_array_2617_ = lean_ctor_get(v_fst_2616_, 0);
v_idx_2618_ = lean_ctor_get(v_fst_2616_, 1);
v_lower_2619_ = lean_ctor_get(v___y_2589_, 0);
lean_inc(v_lower_2619_);
v_upper_2620_ = lean_ctor_get(v___y_2589_, 1);
lean_inc(v_upper_2620_);
lean_dec_ref(v___y_2589_);
v___x_2621_ = l_ByteArray_toByteSlice(v_array_2508_, v_lower_2619_, v_upper_2620_);
v___x_2622_ = lean_byte_array_size(v_array_2617_);
v___x_2623_ = lean_nat_dec_lt(v_idx_2618_, v___x_2622_);
if (v___x_2623_ == 0)
{
v___y_2561_ = v___x_2621_;
v_pos_2562_ = v_fst_2616_;
goto v___jp_2560_;
}
else
{
uint8_t v___x_2624_; uint32_t v___x_2625_; uint32_t v___x_2626_; uint8_t v___x_2627_; 
v___x_2624_ = lean_byte_array_fget(v_array_2617_, v_idx_2618_);
v___x_2625_ = lean_uint8_to_uint32(v___x_2624_);
v___x_2626_ = 32;
v___x_2627_ = lean_uint32_dec_eq(v___x_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
uint32_t v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = 9;
v___x_2629_ = lean_uint32_dec_eq(v___x_2625_, v___x_2628_);
if (v___x_2629_ == 0)
{
v___y_2561_ = v___x_2621_;
v_pos_2562_ = v_fst_2616_;
goto v___jp_2560_;
}
else
{
lean_dec_ref(v___x_2621_);
v_pos_2419_ = v_fst_2616_;
goto v___jp_2418_;
}
}
else
{
lean_dec_ref(v___x_2621_);
v_pos_2419_ = v_fst_2616_;
goto v___jp_2418_;
}
}
}
else
{
lean_object* v_fst_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v___y_2589_);
lean_dec_ref(v_array_2508_);
v_fst_2630_ = lean_ctor_get(v_snd_2613_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_snd_2613_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; 
v_unused_2639_ = lean_ctor_get(v_snd_2613_, 1);
lean_dec(v_unused_2639_);
v___x_2632_ = v_snd_2613_;
v_isShared_2633_ = v_isSharedCheck_2638_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_fst_2630_);
lean_dec(v_snd_2613_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2638_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_box(0);
if (v_isShared_2633_ == 0)
{
lean_ctor_set_tag(v___x_2632_, 1);
lean_ctor_set(v___x_2632_, 1, v___x_2634_);
v___x_2636_ = v___x_2632_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_fst_2630_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
}
}
}
v___jp_2646_:
{
uint8_t v___x_2648_; 
v___x_2648_ = lean_nat_dec_le(v___x_2644_, v___x_2645_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2650_; 
lean_dec(v___x_2644_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 1, v___x_2645_);
lean_ctor_set(v___x_2505_, 0, v___y_2647_);
v___x_2650_ = v___x_2505_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___y_2647_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
v___y_2589_ = v___x_2650_;
goto v___jp_2588_;
}
}
else
{
lean_object* v___x_2653_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 1, v___x_2644_);
lean_ctor_set(v___x_2505_, 0, v___y_2647_);
v___x_2653_ = v___x_2505_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___y_2647_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2644_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
v___y_2589_ = v___x_2653_;
goto v___jp_2588_;
}
}
}
}
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
lean_dec(v_fst_2503_);
lean_dec(v_fst_2502_);
v___x_2657_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_2506_ == 0)
{
lean_ctor_set_tag(v___x_2505_, 1);
lean_ctor_set(v___x_2505_, 1, v___x_2657_);
lean_ctor_set(v___x_2505_, 0, v_a_2417_);
v___x_2659_ = v___x_2505_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2417_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v_fst_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v___x_2498_);
lean_dec_ref(v_a_2417_);
v_fst_2663_ = lean_ctor_get(v_snd_2499_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_snd_2499_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v_snd_2499_, 1);
lean_dec(v_unused_2672_);
v___x_2665_ = v_snd_2499_;
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_fst_2663_);
lean_dec(v_snd_2499_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = lean_box(0);
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 1);
lean_ctor_set(v___x_2665_, 1, v___x_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_fst_2663_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_pos_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
return v___x_2421_;
}
v___jp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2425_, 0, v_pos_2423_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
return v___x_2425_;
}
v___jp_2431_:
{
lean_object* v___x_2435_; 
v___x_2435_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2434_, v___y_2432_);
lean_dec(v___y_2434_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_pos_2436_; lean_object* v_res_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2450_; 
v_pos_2436_ = lean_ctor_get(v___x_2435_, 0);
v_res_2437_ = lean_ctor_get(v___x_2435_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2450_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_res_2437_);
lean_inc(v_pos_2436_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2450_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2441_ = lean_string_utf8_byte_size(v_res_2437_);
lean_inc(v_res_2437_);
v___x_2442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2442_, 0, v_res_2437_);
lean_ctor_set(v___x_2442_, 1, v___x_2430_);
lean_ctor_set(v___x_2442_, 2, v___x_2441_);
v___x_2443_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine_spec__0(v___x_2442_, v___x_2441_);
lean_dec_ref_known(v___x_2442_, 3);
v___x_2444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2444_, 0, v_res_2437_);
lean_ctor_set(v___x_2444_, 1, v___x_2430_);
lean_ctor_set(v___x_2444_, 2, v___x_2443_);
v___x_2445_ = l_String_Slice_toString(v___x_2444_);
lean_dec_ref_known(v___x_2444_, 3);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___y_2433_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v___x_2446_);
v___x_2448_ = v___x_2439_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_pos_2436_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_pos_2451_; lean_object* v_err_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v___y_2433_);
v_pos_2451_ = lean_ctor_get(v___x_2435_, 0);
v_err_2452_ = lean_ctor_get(v___x_2435_, 1);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2435_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_err_2452_);
lean_inc(v_pos_2451_);
lean_dec(v___x_2435_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_pos_2451_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_err_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
v___jp_2460_:
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_string_validate_utf8(v___y_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; 
lean_dec_ref(v___y_2463_);
v___x_2465_ = lean_box(0);
v___y_2432_ = v___y_2461_;
v___y_2433_ = v___y_2462_;
v___y_2434_ = v___x_2465_;
goto v___jp_2431_;
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_string_from_utf8_unchecked(v___y_2463_);
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
v___y_2432_ = v___y_2461_;
v___y_2433_ = v___y_2462_;
v___y_2434_ = v___x_2467_;
goto v___jp_2431_;
}
}
v___jp_2468_:
{
lean_object* v___x_2472_; 
v___x_2472_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___y_2471_, v___y_2470_);
lean_dec(v___y_2471_);
if (lean_obj_tag(v___x_2472_) == 0)
{
if (lean_obj_tag(v___y_2469_) == 0)
{
lean_object* v_pos_2473_; lean_object* v_res_2474_; lean_object* v___x_2475_; 
v_pos_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_pos_2473_);
v_res_2474_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_res_2474_);
lean_dec_ref_known(v___x_2472_, 2);
v___x_2475_ = l_ByteArray_empty;
v___y_2461_ = v_pos_2473_;
v___y_2462_ = v_res_2474_;
v___y_2463_ = v___x_2475_;
goto v___jp_2460_;
}
else
{
lean_object* v_pos_2476_; lean_object* v_res_2477_; lean_object* v_val_2478_; lean_object* v___x_2479_; 
v_pos_2476_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_pos_2476_);
v_res_2477_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_res_2477_);
lean_dec_ref_known(v___x_2472_, 2);
v_val_2478_ = lean_ctor_get(v___y_2469_, 0);
lean_inc(v_val_2478_);
lean_dec_ref_known(v___y_2469_, 1);
v___x_2479_ = l_ByteSlice_toByteArray(v_val_2478_);
v___y_2461_ = v_pos_2476_;
v___y_2462_ = v_res_2477_;
v___y_2463_ = v___x_2479_;
goto v___jp_2460_;
}
}
else
{
lean_object* v_pos_2480_; lean_object* v_err_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v___y_2469_);
v_pos_2480_ = lean_ctor_get(v___x_2472_, 0);
v_err_2481_ = lean_ctor_get(v___x_2472_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2472_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_err_2481_);
lean_inc(v_pos_2480_);
lean_dec(v___x_2472_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_pos_2480_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_err_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
v___jp_2489_:
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = l_ByteSlice_toByteArray(v___y_2490_);
v___x_2494_ = lean_string_validate_utf8(v___x_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; 
lean_dec_ref(v___x_2493_);
v___x_2495_ = lean_box(0);
v___y_2469_ = v_res_2492_;
v___y_2470_ = v_pos_2491_;
v___y_2471_ = v___x_2495_;
goto v___jp_2468_;
}
else
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_string_from_utf8_unchecked(v___x_2493_);
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
v___y_2469_ = v_res_2492_;
v___y_2470_ = v_pos_2491_;
v___y_2471_ = v___x_2497_;
goto v___jp_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___boxed(lean_object* v_limits_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2673_, v_a_2674_);
lean_dec_ref(v_limits_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(lean_object* v_x_2676_, lean_object* v_x_2677_){
_start:
{
if (lean_obj_tag(v_x_2676_) == 0)
{
if (lean_obj_tag(v_x_2677_) == 0)
{
uint8_t v___x_2678_; 
v___x_2678_ = 1;
return v___x_2678_;
}
else
{
uint8_t v___x_2679_; 
v___x_2679_ = 0;
return v___x_2679_;
}
}
else
{
if (lean_obj_tag(v_x_2677_) == 0)
{
uint8_t v___x_2680_; 
v___x_2680_ = 0;
return v___x_2680_;
}
else
{
lean_object* v_val_2681_; lean_object* v_val_2682_; uint8_t v___x_2683_; uint8_t v___x_2684_; uint8_t v___x_2685_; 
v_val_2681_ = lean_ctor_get(v_x_2676_, 0);
v_val_2682_ = lean_ctor_get(v_x_2677_, 0);
v___x_2683_ = lean_unbox(v_val_2681_);
v___x_2684_ = lean_unbox(v_val_2682_);
v___x_2685_ = lean_uint8_dec_eq(v___x_2683_, v___x_2684_);
return v___x_2685_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0___boxed(lean_object* v_x_2686_, lean_object* v_x_2687_){
_start:
{
uint8_t v_res_2688_; lean_object* v_r_2689_; 
v_res_2688_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_x_2686_, v_x_2687_);
lean_dec(v_x_2687_);
lean_dec(v_x_2686_);
v_r_2689_ = lean_box(v_res_2688_);
return v_r_2689_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader(lean_object* v_limits_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_pos_2699_; lean_object* v_res_2700_; lean_object* v___y_2704_; uint8_t v___y_2705_; lean_object* v_pos_2754_; lean_object* v_res_2755_; lean_object* v_array_2760_; lean_object* v_idx_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_array_2760_ = lean_ctor_get(v_a_2697_, 0);
v_idx_2761_ = lean_ctor_get(v_a_2697_, 1);
v___x_2762_ = lean_byte_array_size(v_array_2760_);
v___x_2763_ = lean_nat_dec_lt(v_idx_2761_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_box(0);
v_pos_2754_ = v_a_2697_;
v_res_2755_ = v___x_2764_;
goto v___jp_2753_;
}
else
{
uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = lean_byte_array_fget(v_array_2760_, v_idx_2761_);
v___x_2766_ = lean_box(v___x_2765_);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v_pos_2754_ = v_a_2697_;
v_res_2755_ = v___x_2767_;
goto v___jp_2753_;
}
v___jp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_res_2700_);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_pos_2699_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
return v___x_2702_;
}
v___jp_2703_:
{
if (v___y_2705_ == 0)
{
lean_object* v___x_2706_; 
v___x_2706_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine(v_limits_2696_, v___y_2704_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_pos_2707_; lean_object* v_res_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_pos_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_pos_2707_);
v_res_2708_ = lean_ctor_get(v___x_2706_, 1);
lean_inc(v_res_2708_);
lean_dec_ref_known(v___x_2706_, 2);
v___x_2709_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2710_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2709_, v_pos_2707_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_pos_2711_; 
v_pos_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_pos_2711_);
lean_dec_ref_known(v___x_2710_, 2);
v_pos_2699_ = v_pos_2711_;
v_res_2700_ = v_res_2708_;
goto v___jp_2698_;
}
else
{
lean_object* v_pos_2712_; lean_object* v_err_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_res_2708_);
v_pos_2712_ = lean_ctor_get(v___x_2710_, 0);
v_err_2713_ = lean_ctor_get(v___x_2710_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2710_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_err_2713_);
lean_inc(v_pos_2712_);
lean_dec(v___x_2710_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_pos_2712_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_err_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_pos_2721_; lean_object* v_res_2722_; 
v_pos_2721_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_pos_2721_);
v_res_2722_ = lean_ctor_get(v___x_2706_, 1);
lean_inc(v_res_2722_);
lean_dec_ref_known(v___x_2706_, 2);
v_pos_2699_ = v_pos_2721_;
v_res_2700_ = v_res_2722_;
goto v___jp_2698_;
}
else
{
lean_object* v_pos_2723_; lean_object* v_err_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_pos_2723_ = lean_ctor_get(v___x_2706_, 0);
v_err_2724_ = lean_ctor_get(v___x_2706_, 1);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2706_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_err_2724_);
lean_inc(v_pos_2723_);
lean_dec(v___x_2706_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_pos_2723_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_err_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_2733_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2732_, v___y_2704_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_pos_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2742_; 
v_pos_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v___x_2733_, 1);
lean_dec(v_unused_2743_);
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_pos_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = lean_box(0);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v___x_2738_);
v___x_2740_ = v___x_2736_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_pos_2734_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
else
{
lean_object* v_pos_2744_; lean_object* v_err_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
v_pos_2744_ = lean_ctor_get(v___x_2733_, 0);
v_err_2745_ = lean_ctor_get(v___x_2733_, 1);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2733_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_err_2745_);
lean_inc(v_pos_2744_);
lean_dec(v___x_2733_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_pos_2744_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_err_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
v___jp_2753_:
{
lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__0));
v___x_2757_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2755_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2758_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseSingleHeader___closed__1));
v___x_2759_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_parseSingleHeader_spec__0(v_res_2755_, v___x_2758_);
lean_dec(v_res_2755_);
v___y_2704_ = v_pos_2754_;
v___y_2705_ = v___x_2759_;
goto v___jp_2703_;
}
else
{
lean_dec(v_res_2755_);
v___y_2704_ = v_pos_2754_;
v___y_2705_ = v___x_2757_;
goto v___jp_2703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseSingleHeader___boxed(lean_object* v_limits_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_2768_, v_a_2769_);
lean_dec_ref(v_limits_2768_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair(lean_object* v_a_2775_){
_start:
{
lean_object* v_array_2776_; lean_object* v_idx_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v_array_2776_ = lean_ctor_get(v_a_2775_, 0);
v_idx_2777_ = lean_ctor_get(v_a_2775_, 1);
v___x_2778_ = lean_byte_array_size(v_array_2776_);
v___x_2779_ = lean_nat_dec_lt(v_idx_2777_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2781_, 0, v_a_2775_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
return v___x_2781_;
}
else
{
uint8_t v___x_2782_; uint8_t v_got_2783_; uint8_t v___x_2784_; 
v___x_2782_ = 92;
v_got_2783_ = lean_byte_array_fget(v_array_2776_, v_idx_2777_);
v___x_2784_ = lean_uint8_dec_eq(v_got_2783_, v___x_2782_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__1));
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v_a_2775_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
return v___x_2786_;
}
else
{
lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2820_; 
lean_inc(v_idx_2777_);
lean_inc_ref(v_array_2776_);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_a_2775_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; lean_object* v_unused_2822_; 
v_unused_2821_ = lean_ctor_get(v_a_2775_, 1);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_a_2775_, 0);
lean_dec(v_unused_2822_);
v___x_2788_ = v_a_2775_;
v_isShared_2789_ = v_isSharedCheck_2820_;
goto v_resetjp_2787_;
}
else
{
lean_dec(v_a_2775_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2820_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2790_ = lean_unsigned_to_nat(1u);
v___x_2791_ = lean_nat_add(v_idx_2777_, v___x_2790_);
lean_dec(v_idx_2777_);
v___x_2792_ = lean_nat_dec_lt(v___x_2791_, v___x_2778_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2794_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v___x_2791_);
v___x_2794_ = v___x_2788_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_array_2776_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2791_);
v___x_2794_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
return v___x_2796_;
}
}
else
{
uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2798_ = lean_byte_array_fget(v_array_2776_, v___x_2791_);
v___x_2799_ = lean_nat_add(v___x_2791_, v___x_2790_);
lean_dec(v___x_2791_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v___x_2799_);
v___x_2801_ = v___x_2788_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_array_2776_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; uint32_t v___x_2804_; uint32_t v___x_2811_; uint8_t v___x_2812_; 
v___x_2802_ = lean_box(v___x_2798_);
lean_inc_ref(v___x_2801_);
v___x_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_uint8_to_uint32(v___x_2798_);
v___x_2811_ = 9;
v___x_2812_ = lean_uint32_dec_eq(v___x_2804_, v___x_2811_);
if (v___x_2812_ == 0)
{
uint32_t v___x_2813_; uint8_t v___x_2814_; 
v___x_2813_ = 32;
v___x_2814_ = lean_uint32_dec_eq(v___x_2804_, v___x_2813_);
if (v___x_2814_ == 0)
{
uint32_t v___x_2815_; uint8_t v___x_2816_; 
v___x_2815_ = 33;
v___x_2816_ = lean_uint32_dec_le(v___x_2815_, v___x_2804_);
if (v___x_2816_ == 0)
{
lean_dec_ref_known(v___x_2803_, 2);
goto v___jp_2805_;
}
else
{
uint32_t v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = 126;
v___x_2818_ = lean_uint32_dec_le(v___x_2804_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_dec_ref_known(v___x_2803_, 2);
goto v___jp_2805_;
}
else
{
lean_dec_ref(v___x_2801_);
return v___x_2803_;
}
}
}
else
{
lean_dec_ref(v___x_2801_);
return v___x_2803_;
}
}
else
{
lean_dec_ref(v___x_2801_);
return v___x_2803_;
}
v___jp_2805_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2806_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2807_ = l_Char_quote(v___x_2804_);
v___x_2808_ = lean_string_append(v___x_2806_, v___x_2807_);
lean_dec_ref(v___x_2807_);
v___x_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
v___x_2810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2801_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
return v___x_2810_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(lean_object* v_maxLength_2827_, lean_object* v_buf_2828_, lean_object* v_length_2829_, lean_object* v_a_2830_){
_start:
{
lean_object* v_array_2831_; lean_object* v_idx_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v_array_2831_ = lean_ctor_get(v_a_2830_, 0);
v_idx_2832_ = lean_ctor_get(v_a_2830_, 1);
v___x_2833_ = lean_byte_array_size(v_array_2831_);
v___x_2834_ = lean_nat_dec_lt(v_idx_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_dec(v_length_2829_);
lean_dec_ref(v_buf_2828_);
v___x_2835_ = lean_box(0);
v___x_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2836_, 0, v_a_2830_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
return v___x_2836_;
}
else
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2909_; 
lean_inc(v_idx_2832_);
lean_inc_ref(v_array_2831_);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_a_2830_);
if (v_isSharedCheck_2909_ == 0)
{
lean_object* v_unused_2910_; lean_object* v_unused_2911_; 
v_unused_2910_ = lean_ctor_get(v_a_2830_, 1);
lean_dec(v_unused_2910_);
v_unused_2911_ = lean_ctor_get(v_a_2830_, 0);
lean_dec(v_unused_2911_);
v___x_2838_ = v_a_2830_;
v_isShared_2839_ = v_isSharedCheck_2909_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v_a_2830_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2909_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
uint8_t v_c_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v_it_x27_2844_; 
v_c_2840_ = lean_byte_array_fget(v_array_2831_, v_idx_2832_);
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = lean_nat_add(v_idx_2832_, v___x_2841_);
lean_dec(v_idx_2832_);
lean_inc(v___x_2842_);
lean_inc_ref(v_array_2831_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v___x_2842_);
v_it_x27_2844_ = v___x_2838_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_array_2831_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2842_);
v_it_x27_2844_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
uint8_t v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = 34;
v___x_2860_ = lean_uint8_dec_eq(v_c_2840_, v___x_2859_);
if (v___x_2860_ == 0)
{
uint8_t v___x_2861_; uint8_t v___x_2862_; 
v___x_2861_ = 92;
v___x_2862_ = lean_uint8_dec_eq(v_c_2840_, v___x_2861_);
if (v___x_2862_ == 0)
{
uint32_t v___x_2863_; uint32_t v___x_2869_; uint8_t v___x_2870_; 
lean_dec(v___x_2842_);
lean_dec_ref(v_array_2831_);
v___x_2863_ = lean_uint8_to_uint32(v_c_2840_);
v___x_2869_ = 9;
v___x_2870_ = lean_uint32_dec_eq(v___x_2863_, v___x_2869_);
if (v___x_2870_ == 0)
{
uint32_t v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = 32;
v___x_2872_ = lean_uint32_dec_eq(v___x_2863_, v___x_2871_);
if (v___x_2872_ == 0)
{
uint32_t v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = 33;
v___x_2874_ = lean_uint32_dec_eq(v___x_2863_, v___x_2873_);
if (v___x_2874_ == 0)
{
uint32_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = 35;
v___x_2876_ = lean_uint32_dec_le(v___x_2875_, v___x_2863_);
if (v___x_2876_ == 0)
{
goto v___jp_2864_;
}
else
{
uint32_t v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = 91;
v___x_2878_ = lean_uint32_dec_le(v___x_2863_, v___x_2877_);
if (v___x_2878_ == 0)
{
goto v___jp_2864_;
}
else
{
goto v___jp_2845_;
}
}
}
else
{
goto v___jp_2845_;
}
}
else
{
goto v___jp_2845_;
}
}
else
{
goto v___jp_2845_;
}
v___jp_2864_:
{
uint32_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = 93;
v___x_2866_ = lean_uint32_dec_le(v___x_2865_, v___x_2863_);
if (v___x_2866_ == 0)
{
lean_dec(v_length_2829_);
lean_dec_ref(v_buf_2828_);
goto v___jp_2852_;
}
else
{
uint32_t v___x_2867_; uint8_t v___x_2868_; 
v___x_2867_ = 126;
v___x_2868_ = lean_uint32_dec_le(v___x_2863_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_dec(v_length_2829_);
lean_dec_ref(v_buf_2828_);
goto v___jp_2852_;
}
else
{
goto v___jp_2845_;
}
}
}
}
else
{
uint8_t v___x_2879_; 
v___x_2879_ = lean_nat_dec_lt(v___x_2842_, v___x_2833_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec(v___x_2842_);
lean_dec_ref(v_array_2831_);
lean_dec(v_length_2829_);
lean_dec_ref(v_buf_2828_);
v___x_2880_ = lean_box(0);
v___x_2881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2881_, 0, v_it_x27_2844_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
return v___x_2881_;
}
else
{
uint8_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint32_t v___x_2892_; uint32_t v___x_2899_; uint8_t v___x_2900_; 
lean_dec_ref(v_it_x27_2844_);
v___x_2882_ = lean_byte_array_fget(v_array_2831_, v___x_2842_);
v___x_2883_ = lean_nat_add(v___x_2842_, v___x_2841_);
lean_dec(v___x_2842_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_array_2831_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2892_ = lean_uint8_to_uint32(v___x_2882_);
v___x_2899_ = 9;
v___x_2900_ = lean_uint32_dec_eq(v___x_2892_, v___x_2899_);
if (v___x_2900_ == 0)
{
uint32_t v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = 32;
v___x_2902_ = lean_uint32_dec_eq(v___x_2892_, v___x_2901_);
if (v___x_2902_ == 0)
{
uint32_t v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = 33;
v___x_2904_ = lean_uint32_dec_le(v___x_2903_, v___x_2892_);
if (v___x_2904_ == 0)
{
lean_dec(v_length_2829_);
lean_dec_ref(v_buf_2828_);
goto v___jp_2893_;
}
else
{
uint32_t v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = 126;
v___x_2906_ = lean_uint32_dec_le(v___x_2892_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_dec(v_length_2829_);
lean_dec_ref(v_buf_2828_);
goto v___jp_2893_;
}
else
{
goto v___jp_2885_;
}
}
}
else
{
goto v___jp_2885_;
}
}
else
{
goto v___jp_2885_;
}
v___jp_2885_:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = lean_nat_add(v_length_2829_, v___x_2841_);
lean_dec(v_length_2829_);
v___x_2887_ = lean_nat_dec_lt(v_maxLength_2827_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_byte_array_push(v_buf_2828_, v___x_2882_);
v_buf_2828_ = v___x_2888_;
v_length_2829_ = v___x_2886_;
v_a_2830_ = v___x_2884_;
goto _start;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v___x_2886_);
lean_dec_ref(v_buf_2828_);
v___x_2890_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2884_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
return v___x_2891_;
}
}
v___jp_2893_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2894_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedPair___closed__2));
v___x_2895_ = l_Char_quote(v___x_2892_);
v___x_2896_ = lean_string_append(v___x_2894_, v___x_2895_);
lean_dec_ref(v___x_2895_);
v___x_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2884_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
return v___x_2898_;
}
}
}
}
else
{
lean_object* v___x_2907_; 
lean_dec(v___x_2842_);
lean_dec_ref(v_array_2831_);
lean_dec(v_length_2829_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v_it_x27_2844_);
lean_ctor_set(v___x_2907_, 1, v_buf_2828_);
return v___x_2907_;
}
v___jp_2845_:
{
lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2846_ = lean_nat_add(v_length_2829_, v___x_2841_);
lean_dec(v_length_2829_);
v___x_2847_ = lean_nat_dec_lt(v_maxLength_2827_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_byte_array_push(v_buf_2828_, v_c_2840_);
v_buf_2828_ = v___x_2848_;
v_length_2829_ = v___x_2846_;
v_a_2830_ = v_it_x27_2844_;
goto _start;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_dec(v___x_2846_);
lean_dec_ref(v_buf_2828_);
v___x_2850_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__1));
v___x_2851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_it_x27_2844_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
return v___x_2851_;
}
}
v___jp_2852_:
{
lean_object* v___x_2853_; uint32_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2853_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___closed__2));
v___x_2854_ = lean_uint8_to_uint32(v_c_2840_);
v___x_2855_ = l_Char_quote(v___x_2854_);
v___x_2856_ = lean_string_append(v___x_2853_, v___x_2855_);
lean_dec_ref(v___x_2855_);
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_it_x27_2844_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
return v___x_2858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop___boxed(lean_object* v_maxLength_2912_, lean_object* v_buf_2913_, lean_object* v_length_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2912_, v_buf_2913_, v_length_2914_, v_a_2915_);
lean_dec(v_maxLength_2912_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(lean_object* v_maxLength_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v_array_2922_; lean_object* v_idx_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v_array_2922_ = lean_ctor_get(v_a_2921_, 0);
v_idx_2923_ = lean_ctor_get(v_a_2921_, 1);
v___x_2924_ = lean_byte_array_size(v_array_2922_);
v___x_2925_ = lean_nat_dec_lt(v_idx_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_box(0);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v_a_2921_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
return v___x_2927_;
}
else
{
uint8_t v___x_2928_; uint8_t v_got_2929_; uint8_t v___x_2930_; 
v___x_2928_ = 34;
v_got_2929_ = lean_byte_array_fget(v_array_2922_, v_idx_2923_);
v___x_2930_ = lean_uint8_dec_eq(v_got_2929_, v___x_2928_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___closed__1));
v___x_2932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2932_, 0, v_a_2921_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
return v___x_2932_;
}
else
{
lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2961_; 
lean_inc(v_idx_2923_);
lean_inc_ref(v_array_2922_);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_a_2921_);
if (v_isSharedCheck_2961_ == 0)
{
lean_object* v_unused_2962_; lean_object* v_unused_2963_; 
v_unused_2962_ = lean_ctor_get(v_a_2921_, 1);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v_a_2921_, 0);
lean_dec(v_unused_2963_);
v___x_2934_ = v_a_2921_;
v_isShared_2935_ = v_isSharedCheck_2961_;
goto v_resetjp_2933_;
}
else
{
lean_dec(v_a_2921_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2961_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2936_ = lean_unsigned_to_nat(1u);
v___x_2937_ = lean_nat_add(v_idx_2923_, v___x_2936_);
lean_dec(v_idx_2923_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 1, v___x_2937_);
v___x_2939_ = v___x_2934_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_array_2922_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = l_ByteArray_empty;
v___x_2941_ = lean_unsigned_to_nat(0u);
v___x_2942_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString_loop(v_maxLength_2920_, v___x_2940_, v___x_2941_, v___x_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_pos_2943_; lean_object* v_res_2944_; uint8_t v___x_2945_; 
v_pos_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_pos_2943_);
v_res_2944_ = lean_ctor_get(v___x_2942_, 1);
lean_inc(v_res_2944_);
lean_dec_ref_known(v___x_2942_, 2);
v___x_2945_ = lean_string_validate_utf8(v_res_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
lean_dec(v_res_2944_);
v___x_2946_ = lean_box(0);
v___x_2947_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2946_, v_pos_2943_);
return v___x_2947_;
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_string_from_utf8_unchecked(v_res_2944_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
v___x_2950_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_2949_, v_pos_2943_);
lean_dec_ref_known(v___x_2949_, 1);
return v___x_2950_;
}
}
else
{
lean_object* v_pos_2951_; lean_object* v_err_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_pos_2951_ = lean_ctor_get(v___x_2942_, 0);
v_err_2952_ = lean_ctor_get(v___x_2942_, 1);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2942_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_err_2952_);
lean_inc(v_pos_2951_);
lean_dec(v___x_2942_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_pos_2951_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_err_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString___boxed(lean_object* v_maxLength_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxLength_2964_, v_a_2965_);
lean_dec(v_maxLength_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(lean_object* v___f_2967_, lean_object* v_maxSpaceSequence_2968_, lean_object* v_x_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_pos_2972_; lean_object* v_pos_2976_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_snd_2981_; lean_object* v_snd_2982_; uint8_t v___x_2983_; 
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_2967_, v_maxSpaceSequence_2968_, v___x_2979_, v___y_2970_);
v_snd_2981_ = lean_ctor_get(v___x_2980_, 1);
lean_inc(v_snd_2981_);
lean_dec_ref(v___x_2980_);
v_snd_2982_ = lean_ctor_get(v_snd_2981_, 1);
v___x_2983_ = lean_unbox(v_snd_2982_);
if (v___x_2983_ == 0)
{
lean_object* v_fst_2984_; lean_object* v_array_2985_; lean_object* v_idx_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v_fst_2984_ = lean_ctor_get(v_snd_2981_, 0);
lean_inc(v_fst_2984_);
lean_dec(v_snd_2981_);
v_array_2985_ = lean_ctor_get(v_fst_2984_, 0);
v_idx_2986_ = lean_ctor_get(v_fst_2984_, 1);
v___x_2987_ = lean_byte_array_size(v_array_2985_);
v___x_2988_ = lean_nat_dec_lt(v_idx_2986_, v___x_2987_);
if (v___x_2988_ == 0)
{
v_pos_2972_ = v_fst_2984_;
goto v___jp_2971_;
}
else
{
uint8_t v___x_2989_; uint32_t v___x_2990_; uint32_t v___x_2991_; uint8_t v___x_2992_; 
v___x_2989_ = lean_byte_array_fget(v_array_2985_, v_idx_2986_);
v___x_2990_ = lean_uint8_to_uint32(v___x_2989_);
v___x_2991_ = 32;
v___x_2992_ = lean_uint32_dec_eq(v___x_2990_, v___x_2991_);
if (v___x_2992_ == 0)
{
uint32_t v___x_2993_; uint8_t v___x_2994_; 
v___x_2993_ = 9;
v___x_2994_ = lean_uint32_dec_eq(v___x_2990_, v___x_2993_);
if (v___x_2994_ == 0)
{
v_pos_2972_ = v_fst_2984_;
goto v___jp_2971_;
}
else
{
v_pos_2976_ = v_fst_2984_;
goto v___jp_2975_;
}
}
else
{
v_pos_2976_ = v_fst_2984_;
goto v___jp_2975_;
}
}
}
else
{
lean_object* v_fst_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3003_; 
v_fst_2995_ = lean_ctor_get(v_snd_2981_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_snd_2981_);
if (v_isSharedCheck_3003_ == 0)
{
lean_object* v_unused_3004_; 
v_unused_3004_ = lean_ctor_get(v_snd_2981_, 1);
lean_dec(v_unused_3004_);
v___x_2997_ = v_snd_2981_;
v_isShared_2998_ = v_isSharedCheck_3003_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_fst_2995_);
lean_dec(v_snd_2981_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3003_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2999_ = lean_box(0);
if (v_isShared_2998_ == 0)
{
lean_ctor_set_tag(v___x_2997_, 1);
lean_ctor_set(v___x_2997_, 1, v___x_2999_);
v___x_3001_ = v___x_2997_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_fst_2995_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
v___jp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v_pos_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
return v___x_2974_;
}
v___jp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_pos_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2___boxed(lean_object* v___f_3005_, lean_object* v_maxSpaceSequence_3006_, lean_object* v_x_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3005_, v_maxSpaceSequence_3006_, v_x_3007_, v___y_3008_);
lean_dec(v_maxSpaceSequence_3006_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(lean_object* v_limits_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_pos_3025_; lean_object* v_pos_3029_; lean_object* v___y_3033_; lean_object* v_pos_3034_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3066_; lean_object* v_pos_3067_; lean_object* v_res_3068_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v_lower_3074_; lean_object* v_upper_3075_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v_pos_3091_; lean_object* v_pos_3095_; lean_object* v_maxSpaceSequence_3098_; lean_object* v_maxChunkExtNameLength_3099_; lean_object* v_maxChunkExtValueLength_3100_; lean_object* v___f_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_snd_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3392_; 
v_maxSpaceSequence_3098_ = lean_ctor_get(v_limits_3022_, 8);
v_maxChunkExtNameLength_3099_ = lean_ctor_get(v_limits_3022_, 11);
v_maxChunkExtValueLength_3100_ = lean_ctor_get(v_limits_3022_, 12);
v___f_3101_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__0));
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3101_, v_maxSpaceSequence_3098_, v___x_3102_, v_a_3023_);
v_snd_3104_ = lean_ctor_get(v___x_3103_, 1);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v___x_3103_, 0);
lean_dec(v_unused_3393_);
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3392_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_snd_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3392_;
goto v_resetjp_3105_;
}
v___jp_3024_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_pos_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
return v___x_3027_;
}
v___jp_3028_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3031_, 0, v_pos_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
return v___x_3031_;
}
v___jp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___y_3033_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_pos_3034_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
return v___x_3037_;
}
v___jp_3038_:
{
if (lean_obj_tag(v___y_3040_) == 0)
{
lean_object* v_pos_3041_; lean_object* v_res_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3055_; 
v_pos_3041_ = lean_ctor_get(v___y_3040_, 0);
v_res_3042_ = lean_ctor_get(v___y_3040_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___y_3040_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3044_ = v___y_3040_;
v_isShared_3045_ = v_isSharedCheck_3055_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_res_3042_);
lean_inc(v_pos_3041_);
lean_dec(v___y_3040_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3055_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_res_3042_);
if (lean_obj_tag(v___x_3046_) == 1)
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___y_3039_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v___x_3047_);
v___x_3049_ = v___x_3044_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_pos_3041_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
lean_dec(v___x_3046_);
lean_dec_ref(v___y_3039_);
v___x_3051_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__1));
if (v_isShared_3045_ == 0)
{
lean_ctor_set_tag(v___x_3044_, 1);
lean_ctor_set(v___x_3044_, 1, v___x_3051_);
v___x_3053_ = v___x_3044_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_pos_3041_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_pos_3056_; lean_object* v_err_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v___y_3039_);
v_pos_3056_ = lean_ctor_get(v___y_3040_, 0);
v_err_3057_ = lean_ctor_get(v___y_3040_, 1);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___y_3040_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___y_3040_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_err_3057_);
lean_inc(v_pos_3056_);
lean_dec(v___y_3040_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_pos_3056_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_err_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
v___jp_3065_:
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3068_, v_pos_3067_);
lean_dec(v_res_3068_);
v___y_3039_ = v___y_3066_;
v___y_3040_ = v___x_3069_;
goto v___jp_3038_;
}
v___jp_3070_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v___x_3076_ = l_ByteArray_toByteSlice(v___y_3072_, v_lower_3074_, v_upper_3075_);
v___x_3077_ = l_ByteSlice_toByteArray(v___x_3076_);
v___x_3078_ = lean_string_validate_utf8(v___x_3077_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; 
lean_dec_ref(v___x_3077_);
v___x_3079_ = lean_box(0);
v___y_3066_ = v___y_3071_;
v_pos_3067_ = v___y_3073_;
v_res_3068_ = v___x_3079_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_string_from_utf8_unchecked(v___x_3077_);
v___x_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
v___y_3066_ = v___y_3071_;
v_pos_3067_ = v___y_3073_;
v_res_3068_ = v___x_3081_;
goto v___jp_3065_;
}
}
v___jp_3082_:
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_nat_dec_le(v___y_3083_, v___y_3086_);
if (v___x_3089_ == 0)
{
lean_dec(v___y_3083_);
v___y_3071_ = v___y_3084_;
v___y_3072_ = v___y_3085_;
v___y_3073_ = v___y_3087_;
v_lower_3074_ = v___y_3088_;
v_upper_3075_ = v___y_3086_;
goto v___jp_3070_;
}
else
{
lean_dec(v___y_3086_);
v___y_3071_ = v___y_3084_;
v___y_3072_ = v___y_3085_;
v___y_3073_ = v___y_3087_;
v_lower_3074_ = v___y_3088_;
v_upper_3075_ = v___y_3083_;
goto v___jp_3070_;
}
}
v___jp_3090_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3093_, 0, v_pos_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
return v___x_3093_;
}
v___jp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_ows___closed__1));
v___x_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_pos_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
return v___x_3097_;
}
v_resetjp_3105_:
{
lean_object* v_snd_3108_; uint8_t v___x_3109_; 
v_snd_3108_ = lean_ctor_get(v_snd_3104_, 1);
v___x_3109_ = lean_unbox(v_snd_3108_);
if (v___x_3109_ == 0)
{
lean_object* v_fst_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3380_; 
v_fst_3110_ = lean_ctor_get(v_snd_3104_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_snd_3104_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v_snd_3104_, 1);
lean_dec(v_unused_3381_);
v___x_3112_ = v_snd_3104_;
v_isShared_3113_ = v_isSharedCheck_3380_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_fst_3110_);
lean_dec(v_snd_3104_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3380_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v_array_3114_; lean_object* v_idx_3115_; lean_object* v___f_3116_; lean_object* v___y_3118_; lean_object* v_pos_3119_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v_pos_3154_; lean_object* v_array_3155_; lean_object* v_idx_3156_; lean_object* v_pos_3212_; lean_object* v_res_3213_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v_lower_3279_; lean_object* v_upper_3280_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v_pos_3295_; lean_object* v_pos_3328_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_array_3114_ = lean_ctor_get(v_fst_3110_, 0);
v_idx_3115_ = lean_ctor_get(v_fst_3110_, 1);
v___f_3116_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__0));
v___x_3372_ = lean_byte_array_size(v_array_3114_);
v___x_3373_ = lean_nat_dec_lt(v_idx_3115_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_inc(v_idx_3115_);
lean_inc_ref(v_array_3114_);
v_pos_3328_ = v_fst_3110_;
goto v___jp_3327_;
}
else
{
uint8_t v___x_3374_; uint32_t v___x_3375_; uint32_t v___x_3376_; uint8_t v___x_3377_; 
v___x_3374_ = lean_byte_array_fget(v_array_3114_, v_idx_3115_);
v___x_3375_ = lean_uint8_to_uint32(v___x_3374_);
v___x_3376_ = 32;
v___x_3377_ = lean_uint32_dec_eq(v___x_3375_, v___x_3376_);
if (v___x_3377_ == 0)
{
uint32_t v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = 9;
v___x_3379_ = lean_uint32_dec_eq(v___x_3375_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_inc(v_idx_3115_);
lean_inc_ref(v_array_3114_);
v_pos_3328_ = v_fst_3110_;
goto v___jp_3327_;
}
else
{
lean_del_object(v___x_3112_);
lean_del_object(v___x_3106_);
v_pos_3025_ = v_fst_3110_;
goto v___jp_3024_;
}
}
else
{
lean_del_object(v___x_3112_);
lean_del_object(v___x_3106_);
v_pos_3025_ = v_fst_3110_;
goto v___jp_3024_;
}
}
v___jp_3117_:
{
lean_object* v___x_3120_; 
lean_inc_ref(v_pos_3119_);
v___x_3120_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseQuotedString(v_maxChunkExtValueLength_3100_, v_pos_3119_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_dec_ref(v_pos_3119_);
v___y_3039_ = v___y_3118_;
v___y_3040_ = v___x_3120_;
goto v___jp_3038_;
}
else
{
lean_object* v_pos_3121_; lean_object* v_idx_3122_; lean_object* v_array_3123_; lean_object* v_idx_3124_; uint8_t v___x_3125_; 
v_pos_3121_ = lean_ctor_get(v___x_3120_, 0);
v_idx_3122_ = lean_ctor_get(v_pos_3119_, 1);
lean_inc(v_idx_3122_);
lean_dec_ref(v_pos_3119_);
v_array_3123_ = lean_ctor_get(v_pos_3121_, 0);
v_idx_3124_ = lean_ctor_get(v_pos_3121_, 1);
v___x_3125_ = lean_nat_dec_eq(v_idx_3122_, v_idx_3124_);
lean_dec(v_idx_3122_);
if (v___x_3125_ == 0)
{
v___y_3039_ = v___y_3118_;
v___y_3040_ = v___x_3120_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3148_; 
lean_inc(v_pos_3121_);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3149_ = lean_ctor_get(v___x_3120_, 1);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v___x_3120_, 0);
lean_dec(v_unused_3150_);
v___x_3127_ = v___x_3120_;
v_isShared_3128_ = v_isSharedCheck_3148_;
goto v_resetjp_3126_;
}
else
{
lean_dec(v___x_3120_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3148_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v_snd_3130_; lean_object* v_snd_3131_; uint8_t v___x_3132_; 
lean_inc(v_pos_3121_);
v___x_3129_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3116_, v_maxChunkExtValueLength_3100_, v___x_3102_, v_pos_3121_);
v_snd_3130_ = lean_ctor_get(v___x_3129_, 1);
lean_inc(v_snd_3130_);
v_snd_3131_ = lean_ctor_get(v_snd_3130_, 1);
v___x_3132_ = lean_unbox(v_snd_3131_);
if (v___x_3132_ == 0)
{
lean_object* v_fst_3133_; lean_object* v_fst_3134_; uint8_t v___x_3135_; 
v_fst_3133_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_fst_3133_);
lean_dec_ref(v___x_3129_);
v_fst_3134_ = lean_ctor_get(v_snd_3130_, 0);
lean_inc(v_fst_3134_);
lean_dec(v_snd_3130_);
v___x_3135_ = lean_nat_dec_eq(v_fst_3133_, v___x_3102_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
lean_inc(v_idx_3124_);
lean_inc_ref(v_array_3123_);
lean_del_object(v___x_3127_);
lean_dec(v_pos_3121_);
v___x_3136_ = lean_nat_add(v_idx_3124_, v_fst_3133_);
lean_dec(v_fst_3133_);
v___x_3137_ = lean_byte_array_size(v_array_3123_);
v___x_3138_ = lean_nat_dec_le(v_idx_3124_, v___x_3102_);
if (v___x_3138_ == 0)
{
v___y_3083_ = v___x_3136_;
v___y_3084_ = v___y_3118_;
v___y_3085_ = v_array_3123_;
v___y_3086_ = v___x_3137_;
v___y_3087_ = v_fst_3134_;
v___y_3088_ = v_idx_3124_;
goto v___jp_3082_;
}
else
{
lean_dec(v_idx_3124_);
v___y_3083_ = v___x_3136_;
v___y_3084_ = v___y_3118_;
v___y_3085_ = v_array_3123_;
v___y_3086_ = v___x_3137_;
v___y_3087_ = v_fst_3134_;
v___y_3088_ = v___x_3102_;
goto v___jp_3082_;
}
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
lean_dec(v_fst_3134_);
lean_dec(v_fst_3133_);
lean_dec_ref(v___y_3118_);
v___x_3139_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 1, v___x_3139_);
v___x_3141_ = v___x_3127_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_pos_3121_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
else
{
lean_object* v_fst_3143_; lean_object* v___x_3144_; lean_object* v___x_3146_; 
lean_dec_ref(v___x_3129_);
lean_dec(v_pos_3121_);
lean_dec_ref(v___y_3118_);
v_fst_3143_ = lean_ctor_get(v_snd_3130_, 0);
lean_inc(v_fst_3143_);
lean_dec(v_snd_3130_);
v___x_3144_ = lean_box(0);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 1, v___x_3144_);
lean_ctor_set(v___x_3127_, 0, v_fst_3143_);
v___x_3146_ = v___x_3127_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_fst_3143_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
}
v___jp_3151_:
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = lean_byte_array_size(v_array_3155_);
v___x_3158_ = lean_nat_dec_lt(v_idx_3156_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
lean_dec(v_idx_3156_);
lean_dec_ref(v_array_3155_);
lean_dec_ref(v___y_3152_);
v___x_3159_ = lean_box(0);
if (v_isShared_3113_ == 0)
{
lean_ctor_set_tag(v___x_3112_, 1);
lean_ctor_set(v___x_3112_, 1, v___x_3159_);
lean_ctor_set(v___x_3112_, 0, v_pos_3154_);
v___x_3161_ = v___x_3112_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_pos_3154_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
else
{
uint8_t v___x_3163_; uint8_t v_got_3164_; uint8_t v___x_3165_; 
v___x_3163_ = 61;
v_got_3164_ = lean_byte_array_fget(v_array_3155_, v_idx_3156_);
v___x_3165_ = lean_uint8_dec_eq(v_got_3164_, v___x_3163_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
lean_dec(v_idx_3156_);
lean_dec_ref(v_array_3155_);
lean_dec_ref(v___y_3152_);
v___x_3166_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__3));
if (v_isShared_3113_ == 0)
{
lean_ctor_set_tag(v___x_3112_, 1);
lean_ctor_set(v___x_3112_, 1, v___x_3166_);
lean_ctor_set(v___x_3112_, 0, v_pos_3154_);
v___x_3168_ = v___x_3112_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_pos_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3173_; 
lean_dec_ref(v_pos_3154_);
v___x_3170_ = lean_unsigned_to_nat(1u);
v___x_3171_ = lean_nat_add(v_idx_3156_, v___x_3170_);
lean_dec(v_idx_3156_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 1, v___x_3171_);
lean_ctor_set(v___x_3112_, 0, v_array_3155_);
v___x_3173_ = v___x_3112_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_array_3155_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; 
v___x_3174_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3101_, v_maxSpaceSequence_3098_, v___y_3153_, v___x_3173_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_pos_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3199_; 
v_pos_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v___x_3174_, 1);
lean_dec(v_unused_3200_);
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3199_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_pos_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3199_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v_snd_3180_; lean_object* v_snd_3181_; uint8_t v___x_3182_; 
v___x_3179_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3101_, v_maxSpaceSequence_3098_, v___x_3102_, v_pos_3175_);
v_snd_3180_ = lean_ctor_get(v___x_3179_, 1);
lean_inc(v_snd_3180_);
lean_dec_ref(v___x_3179_);
v_snd_3181_ = lean_ctor_get(v_snd_3180_, 1);
v___x_3182_ = lean_unbox(v_snd_3181_);
if (v___x_3182_ == 0)
{
lean_object* v_fst_3183_; lean_object* v_array_3184_; lean_object* v_idx_3185_; lean_object* v___x_3186_; uint8_t v___x_3187_; 
lean_del_object(v___x_3177_);
v_fst_3183_ = lean_ctor_get(v_snd_3180_, 0);
lean_inc(v_fst_3183_);
lean_dec(v_snd_3180_);
v_array_3184_ = lean_ctor_get(v_fst_3183_, 0);
v_idx_3185_ = lean_ctor_get(v_fst_3183_, 1);
v___x_3186_ = lean_byte_array_size(v_array_3184_);
v___x_3187_ = lean_nat_dec_lt(v_idx_3185_, v___x_3186_);
if (v___x_3187_ == 0)
{
v___y_3118_ = v___y_3152_;
v_pos_3119_ = v_fst_3183_;
goto v___jp_3117_;
}
else
{
uint8_t v___x_3188_; uint32_t v___x_3189_; uint32_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3188_ = lean_byte_array_fget(v_array_3184_, v_idx_3185_);
v___x_3189_ = lean_uint8_to_uint32(v___x_3188_);
v___x_3190_ = 32;
v___x_3191_ = lean_uint32_dec_eq(v___x_3189_, v___x_3190_);
if (v___x_3191_ == 0)
{
uint32_t v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = 9;
v___x_3193_ = lean_uint32_dec_eq(v___x_3189_, v___x_3192_);
if (v___x_3193_ == 0)
{
v___y_3118_ = v___y_3152_;
v_pos_3119_ = v_fst_3183_;
goto v___jp_3117_;
}
else
{
lean_dec_ref(v___y_3152_);
v_pos_3091_ = v_fst_3183_;
goto v___jp_3090_;
}
}
else
{
lean_dec_ref(v___y_3152_);
v_pos_3091_ = v_fst_3183_;
goto v___jp_3090_;
}
}
}
else
{
lean_object* v_fst_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_dec_ref(v___y_3152_);
v_fst_3194_ = lean_ctor_get(v_snd_3180_, 0);
lean_inc(v_fst_3194_);
lean_dec(v_snd_3180_);
v___x_3195_ = lean_box(0);
if (v_isShared_3178_ == 0)
{
lean_ctor_set_tag(v___x_3177_, 1);
lean_ctor_set(v___x_3177_, 1, v___x_3195_);
lean_ctor_set(v___x_3177_, 0, v_fst_3194_);
v___x_3197_ = v___x_3177_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_fst_3194_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_object* v_pos_3201_; lean_object* v_err_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v___y_3152_);
v_pos_3201_ = lean_ctor_get(v___x_3174_, 0);
v_err_3202_ = lean_ctor_get(v___x_3174_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3174_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_err_3202_);
lean_inc(v_pos_3201_);
lean_dec(v___x_3174_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_pos_3201_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_err_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
}
v___jp_3211_:
{
lean_object* v___x_3214_; 
v___x_3214_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v_res_3213_, v_pos_3212_);
lean_dec(v_res_3213_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_pos_3215_; lean_object* v_res_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_pos_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_pos_3215_);
v_res_3216_ = lean_ctor_get(v___x_3214_, 1);
lean_inc(v_res_3216_);
lean_dec_ref_known(v___x_3214_, 2);
v___x_3217_ = lean_box(0);
v___x_3218_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___lam__2(v___f_3101_, v_maxSpaceSequence_3098_, v___x_3217_, v_pos_3215_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_pos_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3256_; 
v_pos_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3256_ == 0)
{
lean_object* v_unused_3257_; 
v_unused_3257_ = lean_ctor_get(v___x_3218_, 1);
lean_dec(v_unused_3257_);
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3256_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_pos_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3256_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_res_3216_);
if (lean_obj_tag(v___x_3223_) == 1)
{
lean_object* v_val_3224_; lean_object* v_array_3225_; lean_object* v_idx_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v_val_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_val_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v_array_3225_ = lean_ctor_get(v_pos_3219_, 0);
v_idx_3226_ = lean_ctor_get(v_pos_3219_, 1);
v___x_3227_ = lean_byte_array_size(v_array_3225_);
v___x_3228_ = lean_nat_dec_lt(v_idx_3226_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_del_object(v___x_3221_);
lean_del_object(v___x_3112_);
v___y_3033_ = v_val_3224_;
v_pos_3034_ = v_pos_3219_;
goto v___jp_3032_;
}
else
{
uint8_t v___x_3229_; uint8_t v___x_3230_; uint8_t v___x_3231_; 
v___x_3229_ = lean_byte_array_fget(v_array_3225_, v_idx_3226_);
v___x_3230_ = 61;
v___x_3231_ = lean_uint8_dec_eq(v___x_3229_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_del_object(v___x_3221_);
lean_del_object(v___x_3112_);
v___y_3033_ = v_val_3224_;
v_pos_3034_ = v_pos_3219_;
goto v___jp_3032_;
}
else
{
lean_object* v___x_3232_; lean_object* v_snd_3233_; lean_object* v_snd_3234_; uint8_t v___x_3235_; 
v___x_3232_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3101_, v_maxSpaceSequence_3098_, v___x_3102_, v_pos_3219_);
v_snd_3233_ = lean_ctor_get(v___x_3232_, 1);
lean_inc(v_snd_3233_);
lean_dec_ref(v___x_3232_);
v_snd_3234_ = lean_ctor_get(v_snd_3233_, 1);
v___x_3235_ = lean_unbox(v_snd_3234_);
if (v___x_3235_ == 0)
{
lean_object* v_fst_3236_; lean_object* v_array_3237_; lean_object* v_idx_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; 
lean_del_object(v___x_3221_);
v_fst_3236_ = lean_ctor_get(v_snd_3233_, 0);
lean_inc(v_fst_3236_);
lean_dec(v_snd_3233_);
v_array_3237_ = lean_ctor_get(v_fst_3236_, 0);
v_idx_3238_ = lean_ctor_get(v_fst_3236_, 1);
v___x_3239_ = lean_byte_array_size(v_array_3237_);
v___x_3240_ = lean_nat_dec_lt(v_idx_3238_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_inc(v_idx_3238_);
lean_inc_ref(v_array_3237_);
v___y_3152_ = v_val_3224_;
v___y_3153_ = v___x_3217_;
v_pos_3154_ = v_fst_3236_;
v_array_3155_ = v_array_3237_;
v_idx_3156_ = v_idx_3238_;
goto v___jp_3151_;
}
else
{
uint8_t v___x_3241_; uint32_t v___x_3242_; uint32_t v___x_3243_; uint8_t v___x_3244_; 
v___x_3241_ = lean_byte_array_fget(v_array_3237_, v_idx_3238_);
v___x_3242_ = lean_uint8_to_uint32(v___x_3241_);
v___x_3243_ = 32;
v___x_3244_ = lean_uint32_dec_eq(v___x_3242_, v___x_3243_);
if (v___x_3244_ == 0)
{
uint32_t v___x_3245_; uint8_t v___x_3246_; 
v___x_3245_ = 9;
v___x_3246_ = lean_uint32_dec_eq(v___x_3242_, v___x_3245_);
if (v___x_3246_ == 0)
{
lean_inc(v_idx_3238_);
lean_inc_ref(v_array_3237_);
v___y_3152_ = v_val_3224_;
v___y_3153_ = v___x_3217_;
v_pos_3154_ = v_fst_3236_;
v_array_3155_ = v_array_3237_;
v_idx_3156_ = v_idx_3238_;
goto v___jp_3151_;
}
else
{
lean_dec(v_val_3224_);
lean_del_object(v___x_3112_);
v_pos_3095_ = v_fst_3236_;
goto v___jp_3094_;
}
}
else
{
lean_dec(v_val_3224_);
lean_del_object(v___x_3112_);
v_pos_3095_ = v_fst_3236_;
goto v___jp_3094_;
}
}
}
else
{
lean_object* v_fst_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
lean_dec(v_val_3224_);
lean_del_object(v___x_3112_);
v_fst_3247_ = lean_ctor_get(v_snd_3233_, 0);
lean_inc(v_fst_3247_);
lean_dec(v_snd_3233_);
v___x_3248_ = lean_box(0);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 1, v___x_3248_);
lean_ctor_set(v___x_3221_, 0, v_fst_3247_);
v___x_3250_ = v___x_3221_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_fst_3247_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3254_; 
lean_dec(v___x_3223_);
lean_del_object(v___x_3112_);
v___x_3252_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__5));
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 1, v___x_3252_);
v___x_3254_ = v___x_3221_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_pos_3219_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
else
{
lean_object* v_pos_3258_; lean_object* v_err_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_res_3216_);
lean_del_object(v___x_3112_);
v_pos_3258_ = lean_ctor_get(v___x_3218_, 0);
v_err_3259_ = lean_ctor_get(v___x_3218_, 1);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3218_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_err_3259_);
lean_inc(v_pos_3258_);
lean_dec(v___x_3218_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_pos_3258_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_err_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_object* v_pos_3267_; lean_object* v_err_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_del_object(v___x_3112_);
v_pos_3267_ = lean_ctor_get(v___x_3214_, 0);
v_err_3268_ = lean_ctor_get(v___x_3214_, 1);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3214_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_err_3268_);
lean_inc(v_pos_3267_);
lean_dec(v___x_3214_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_pos_3267_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_err_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
v___jp_3276_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3281_ = l_ByteArray_toByteSlice(v___y_3278_, v_lower_3279_, v_upper_3280_);
v___x_3282_ = l_ByteSlice_toByteArray(v___x_3281_);
v___x_3283_ = lean_string_validate_utf8(v___x_3282_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; 
lean_dec_ref(v___x_3282_);
v___x_3284_ = lean_box(0);
v_pos_3212_ = v___y_3277_;
v_res_3213_ = v___x_3284_;
goto v___jp_3211_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_string_from_utf8_unchecked(v___x_3282_);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
v_pos_3212_ = v___y_3277_;
v_res_3213_ = v___x_3286_;
goto v___jp_3211_;
}
}
v___jp_3287_:
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_nat_dec_le(v___y_3288_, v___y_3290_);
if (v___x_3293_ == 0)
{
lean_dec(v___y_3288_);
v___y_3277_ = v___y_3289_;
v___y_3278_ = v___y_3291_;
v_lower_3279_ = v___y_3292_;
v_upper_3280_ = v___y_3290_;
goto v___jp_3276_;
}
else
{
lean_dec(v___y_3290_);
v___y_3277_ = v___y_3289_;
v___y_3278_ = v___y_3291_;
v_lower_3279_ = v___y_3292_;
v_upper_3280_ = v___y_3288_;
goto v___jp_3276_;
}
}
v___jp_3294_:
{
lean_object* v___x_3296_; lean_object* v_snd_3297_; lean_object* v_snd_3298_; uint8_t v___x_3299_; 
lean_inc_ref(v_pos_3295_);
v___x_3296_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3116_, v_maxChunkExtNameLength_3099_, v___x_3102_, v_pos_3295_);
v_snd_3297_ = lean_ctor_get(v___x_3296_, 1);
lean_inc(v_snd_3297_);
v_snd_3298_ = lean_ctor_get(v_snd_3297_, 1);
v___x_3299_ = lean_unbox(v_snd_3298_);
if (v___x_3299_ == 0)
{
lean_object* v_fst_3300_; lean_object* v_fst_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3315_; 
v_fst_3300_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_fst_3300_);
lean_dec_ref(v___x_3296_);
v_fst_3301_ = lean_ctor_get(v_snd_3297_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_snd_3297_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v_snd_3297_, 1);
lean_dec(v_unused_3316_);
v___x_3303_ = v_snd_3297_;
v_isShared_3304_ = v_isSharedCheck_3315_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_fst_3301_);
lean_dec(v_snd_3297_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3315_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_nat_dec_eq(v_fst_3300_, v___x_3102_);
if (v___x_3305_ == 0)
{
lean_object* v_array_3306_; lean_object* v_idx_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
lean_del_object(v___x_3303_);
v_array_3306_ = lean_ctor_get(v_pos_3295_, 0);
lean_inc_ref(v_array_3306_);
v_idx_3307_ = lean_ctor_get(v_pos_3295_, 1);
lean_inc(v_idx_3307_);
lean_dec_ref(v_pos_3295_);
v___x_3308_ = lean_nat_add(v_idx_3307_, v_fst_3300_);
lean_dec(v_fst_3300_);
v___x_3309_ = lean_byte_array_size(v_array_3306_);
v___x_3310_ = lean_nat_dec_le(v_idx_3307_, v___x_3102_);
if (v___x_3310_ == 0)
{
v___y_3288_ = v___x_3308_;
v___y_3289_ = v_fst_3301_;
v___y_3290_ = v___x_3309_;
v___y_3291_ = v_array_3306_;
v___y_3292_ = v_idx_3307_;
goto v___jp_3287_;
}
else
{
lean_dec(v_idx_3307_);
v___y_3288_ = v___x_3308_;
v___y_3289_ = v_fst_3301_;
v___y_3290_ = v___x_3309_;
v___y_3291_ = v_array_3306_;
v___y_3292_ = v___x_3102_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_dec(v_fst_3301_);
lean_dec(v_fst_3300_);
lean_del_object(v___x_3112_);
v___x_3311_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseToken___closed__2));
if (v_isShared_3304_ == 0)
{
lean_ctor_set_tag(v___x_3303_, 1);
lean_ctor_set(v___x_3303_, 1, v___x_3311_);
lean_ctor_set(v___x_3303_, 0, v_pos_3295_);
v___x_3313_ = v___x_3303_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_pos_3295_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_object* v_fst_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3325_; 
lean_dec_ref(v___x_3296_);
lean_dec_ref(v_pos_3295_);
lean_del_object(v___x_3112_);
v_fst_3317_ = lean_ctor_get(v_snd_3297_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_snd_3297_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; 
v_unused_3326_ = lean_ctor_get(v_snd_3297_, 1);
lean_dec(v_unused_3326_);
v___x_3319_ = v_snd_3297_;
v_isShared_3320_ = v_isSharedCheck_3325_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_fst_3317_);
lean_dec(v_snd_3297_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3325_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3323_; 
v___x_3321_ = lean_box(0);
if (v_isShared_3320_ == 0)
{
lean_ctor_set_tag(v___x_3319_, 1);
lean_ctor_set(v___x_3319_, 1, v___x_3321_);
v___x_3323_ = v___x_3319_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_fst_3317_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
v___jp_3327_:
{
lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3329_ = lean_byte_array_size(v_array_3114_);
v___x_3330_ = lean_nat_dec_lt(v_idx_3115_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
lean_dec(v_idx_3115_);
lean_dec_ref(v_array_3114_);
lean_del_object(v___x_3112_);
v___x_3331_ = lean_box(0);
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 1);
lean_ctor_set(v___x_3106_, 1, v___x_3331_);
lean_ctor_set(v___x_3106_, 0, v_pos_3328_);
v___x_3333_ = v___x_3106_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_pos_3328_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
else
{
uint8_t v___x_3335_; uint8_t v_got_3336_; uint8_t v___x_3337_; 
v___x_3335_ = 59;
v_got_3336_ = lean_byte_array_fget(v_array_3114_, v_idx_3115_);
v___x_3337_ = lean_uint8_dec_eq(v_got_3336_, v___x_3335_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
lean_dec(v_idx_3115_);
lean_dec_ref(v_array_3114_);
lean_del_object(v___x_3112_);
v___x_3338_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___closed__7));
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 1);
lean_ctor_set(v___x_3106_, 1, v___x_3338_);
lean_ctor_set(v___x_3106_, 0, v_pos_3328_);
v___x_3340_ = v___x_3106_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_pos_3328_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
else
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
lean_dec_ref(v_pos_3328_);
v___x_3342_ = lean_unsigned_to_nat(1u);
v___x_3343_ = lean_nat_add(v_idx_3115_, v___x_3342_);
lean_dec(v_idx_3115_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 1, v___x_3343_);
lean_ctor_set(v___x_3106_, 0, v_array_3114_);
v___x_3345_ = v___x_3106_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_array_3114_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v_snd_3347_; lean_object* v_snd_3348_; uint8_t v___x_3349_; 
v___x_3346_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3101_, v_maxSpaceSequence_3098_, v___x_3102_, v___x_3345_);
v_snd_3347_ = lean_ctor_get(v___x_3346_, 1);
lean_inc(v_snd_3347_);
lean_dec_ref(v___x_3346_);
v_snd_3348_ = lean_ctor_get(v_snd_3347_, 1);
v___x_3349_ = lean_unbox(v_snd_3348_);
if (v___x_3349_ == 0)
{
lean_object* v_fst_3350_; lean_object* v_array_3351_; lean_object* v_idx_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v_fst_3350_ = lean_ctor_get(v_snd_3347_, 0);
lean_inc(v_fst_3350_);
lean_dec(v_snd_3347_);
v_array_3351_ = lean_ctor_get(v_fst_3350_, 0);
v_idx_3352_ = lean_ctor_get(v_fst_3350_, 1);
v___x_3353_ = lean_byte_array_size(v_array_3351_);
v___x_3354_ = lean_nat_dec_lt(v_idx_3352_, v___x_3353_);
if (v___x_3354_ == 0)
{
v_pos_3295_ = v_fst_3350_;
goto v___jp_3294_;
}
else
{
uint8_t v___x_3355_; uint32_t v___x_3356_; uint32_t v___x_3357_; uint8_t v___x_3358_; 
v___x_3355_ = lean_byte_array_fget(v_array_3351_, v_idx_3352_);
v___x_3356_ = lean_uint8_to_uint32(v___x_3355_);
v___x_3357_ = 32;
v___x_3358_ = lean_uint32_dec_eq(v___x_3356_, v___x_3357_);
if (v___x_3358_ == 0)
{
uint32_t v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = 9;
v___x_3360_ = lean_uint32_dec_eq(v___x_3356_, v___x_3359_);
if (v___x_3360_ == 0)
{
v_pos_3295_ = v_fst_3350_;
goto v___jp_3294_;
}
else
{
lean_del_object(v___x_3112_);
v_pos_3029_ = v_fst_3350_;
goto v___jp_3028_;
}
}
else
{
lean_del_object(v___x_3112_);
v_pos_3029_ = v_fst_3350_;
goto v___jp_3028_;
}
}
}
else
{
lean_object* v_fst_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3369_; 
lean_del_object(v___x_3112_);
v_fst_3361_ = lean_ctor_get(v_snd_3347_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_snd_3347_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; 
v_unused_3370_ = lean_ctor_get(v_snd_3347_, 1);
lean_dec(v_unused_3370_);
v___x_3363_ = v_snd_3347_;
v_isShared_3364_ = v_isSharedCheck_3369_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_fst_3361_);
lean_dec(v_snd_3347_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3369_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___x_3367_; 
v___x_3365_ = lean_box(0);
if (v_isShared_3364_ == 0)
{
lean_ctor_set_tag(v___x_3363_, 1);
lean_ctor_set(v___x_3363_, 1, v___x_3365_);
v___x_3367_ = v___x_3363_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_fst_3361_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
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
lean_object* v_fst_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3390_; 
lean_del_object(v___x_3106_);
v_fst_3382_ = lean_ctor_get(v_snd_3104_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_snd_3104_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; 
v_unused_3391_ = lean_ctor_get(v_snd_3104_, 1);
lean_dec(v_unused_3391_);
v___x_3384_ = v_snd_3104_;
v_isShared_3385_ = v_isSharedCheck_3390_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_fst_3382_);
lean_dec(v_snd_3104_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3390_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3386_ = lean_box(0);
if (v_isShared_3385_ == 0)
{
lean_ctor_set_tag(v___x_3384_, 1);
lean_ctor_set(v___x_3384_, 1, v___x_3386_);
v___x_3388_ = v___x_3384_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_fst_3382_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt___boxed(lean_object* v_limits_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3394_, v_a_3395_);
lean_dec_ref(v_limits_3394_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0(lean_object* v_limits_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_pos_3400_; lean_object* v_err_3401_; lean_object* v___x_3417_; 
lean_inc_ref(v___y_3398_);
v___x_3417_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseChunkExt(v_limits_3397_, v___y_3398_);
if (lean_obj_tag(v___x_3417_) == 0)
{
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_pos_3418_; lean_object* v_res_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v___y_3398_);
v_pos_3418_ = lean_ctor_get(v___x_3417_, 0);
v_res_3419_ = lean_ctor_get(v___x_3417_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3421_ = v___x_3417_;
v_isShared_3422_ = v_isSharedCheck_3427_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_res_3419_);
lean_inc(v_pos_3418_);
lean_dec(v___x_3417_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3427_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3423_, 0, v_res_3419_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 1, v___x_3423_);
v___x_3425_ = v___x_3421_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_pos_3418_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
else
{
lean_object* v_pos_3428_; lean_object* v_err_3429_; 
v_pos_3428_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_pos_3428_);
v_err_3429_ = lean_ctor_get(v___x_3417_, 1);
lean_inc(v_err_3429_);
lean_dec_ref_known(v___x_3417_, 2);
v_pos_3400_ = v_pos_3428_;
v_err_3401_ = v_err_3429_;
goto v___jp_3399_;
}
}
else
{
lean_object* v_err_3430_; 
v_err_3430_ = lean_ctor_get(v___x_3417_, 1);
lean_inc(v_err_3430_);
lean_dec_ref_known(v___x_3417_, 2);
lean_inc_ref(v___y_3398_);
v_pos_3400_ = v___y_3398_;
v_err_3401_ = v_err_3430_;
goto v___jp_3399_;
}
v___jp_3399_:
{
lean_object* v_idx_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3415_; 
v_idx_3402_ = lean_ctor_get(v___y_3398_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___y_3398_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v___y_3398_, 0);
lean_dec(v_unused_3416_);
v___x_3404_ = v___y_3398_;
v_isShared_3405_ = v_isSharedCheck_3415_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_idx_3402_);
lean_dec(v___y_3398_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3415_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_idx_3406_; uint8_t v___x_3407_; 
v_idx_3406_ = lean_ctor_get(v_pos_3400_, 1);
v___x_3407_ = lean_nat_dec_eq(v_idx_3402_, v_idx_3406_);
lean_dec(v_idx_3402_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3409_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set_tag(v___x_3404_, 1);
lean_ctor_set(v___x_3404_, 1, v_err_3401_);
lean_ctor_set(v___x_3404_, 0, v_pos_3400_);
v___x_3409_ = v___x_3404_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_pos_3400_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_err_3401_);
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
lean_object* v___x_3411_; lean_object* v___x_3413_; 
lean_dec(v_err_3401_);
v___x_3411_ = lean_box(0);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 1, v___x_3411_);
lean_ctor_set(v___x_3404_, 0, v_pos_3400_);
v___x_3413_ = v___x_3404_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_pos_3400_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed(lean_object* v_limits_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Std_Http_Protocol_H1_parseChunkSize___lam__0(v_limits_3431_, v___y_3432_);
lean_dec_ref(v_limits_3431_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSize(lean_object* v_limits_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v___x_3436_; 
v___x_3436_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_hex(v_a_3435_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_pos_3437_; lean_object* v_res_3438_; lean_object* v_maxChunkExtensions_3439_; lean_object* v___f_3440_; lean_object* v___x_3441_; 
v_pos_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_pos_3437_);
v_res_3438_ = lean_ctor_get(v___x_3436_, 1);
lean_inc(v_res_3438_);
lean_dec_ref_known(v___x_3436_, 2);
v_maxChunkExtensions_3439_ = lean_ctor_get(v_limits_3434_, 10);
lean_inc(v_maxChunkExtensions_3439_);
v___f_3440_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_parseChunkSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3440_, 0, v_limits_3434_);
v___x_3441_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___f_3440_, v_maxChunkExtensions_3439_, v_pos_3437_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_pos_3442_; lean_object* v_res_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_pos_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_pos_3442_);
v_res_3443_ = lean_ctor_get(v___x_3441_, 1);
lean_inc(v_res_3443_);
lean_dec_ref_known(v___x_3441_, 2);
v___x_3444_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3445_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3444_, v_pos_3442_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_pos_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3454_; 
v_pos_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v___x_3445_, 1);
lean_dec(v_unused_3455_);
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_pos_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v_res_3438_);
lean_ctor_set(v___x_3450_, 1, v_res_3443_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 1, v___x_3450_);
v___x_3452_ = v___x_3448_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_pos_3446_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
else
{
lean_object* v_pos_3456_; lean_object* v_err_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_res_3443_);
lean_dec(v_res_3438_);
v_pos_3456_ = lean_ctor_get(v___x_3445_, 0);
v_err_3457_ = lean_ctor_get(v___x_3445_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3445_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_err_3457_);
lean_inc(v_pos_3456_);
lean_dec(v___x_3445_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_pos_3456_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_err_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
else
{
lean_object* v_pos_3465_; lean_object* v_err_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_res_3438_);
v_pos_3465_ = lean_ctor_get(v___x_3441_, 0);
v_err_3466_ = lean_ctor_get(v___x_3441_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3441_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_err_3466_);
lean_inc(v_pos_3465_);
lean_dec(v___x_3441_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_pos_3465_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_err_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
else
{
lean_object* v_pos_3474_; lean_object* v_err_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref(v_limits_3434_);
v_pos_3474_ = lean_ctor_get(v___x_3436_, 0);
v_err_3475_ = lean_ctor_get(v___x_3436_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3436_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_err_3475_);
lean_inc(v_pos_3474_);
lean_dec(v___x_3436_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(lean_object* v_x_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_obj_tag_nat(v_x_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl___boxed(lean_object* v_x_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Std_Http_Protocol_H1_TakeResult_ctorIdx___impl(v_x_3485_);
lean_dec_ref(v_x_3485_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(lean_object* v_t_3487_, lean_object* v_k_3488_){
_start:
{
if (lean_obj_tag(v_t_3487_) == 0)
{
lean_object* v_data_3489_; lean_object* v___x_3490_; 
v_data_3489_ = lean_ctor_get(v_t_3487_, 0);
lean_inc_ref(v_data_3489_);
lean_dec_ref_known(v_t_3487_, 1);
v___x_3490_ = lean_apply_1(v_k_3488_, v_data_3489_);
return v___x_3490_;
}
else
{
lean_object* v_data_3491_; lean_object* v_remaining_3492_; lean_object* v___x_3493_; 
v_data_3491_ = lean_ctor_get(v_t_3487_, 0);
lean_inc_ref(v_data_3491_);
v_remaining_3492_ = lean_ctor_get(v_t_3487_, 1);
lean_inc(v_remaining_3492_);
lean_dec_ref_known(v_t_3487_, 2);
v___x_3493_ = lean_apply_2(v_k_3488_, v_data_3491_, v_remaining_3492_);
return v___x_3493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim(lean_object* v_motive_3494_, lean_object* v_ctorIdx_3495_, lean_object* v_t_3496_, lean_object* v_h_3497_, lean_object* v_k_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3496_, v_k_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_ctorElim___boxed(lean_object* v_motive_3500_, lean_object* v_ctorIdx_3501_, lean_object* v_t_3502_, lean_object* v_h_3503_, lean_object* v_k_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim(v_motive_3500_, v_ctorIdx_3501_, v_t_3502_, v_h_3503_, v_k_3504_);
lean_dec(v_ctorIdx_3501_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim___redArg(lean_object* v_t_3506_, lean_object* v_complete_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3506_, v_complete_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_complete_elim(lean_object* v_motive_3509_, lean_object* v_t_3510_, lean_object* v_h_3511_, lean_object* v_complete_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3510_, v_complete_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim___redArg(lean_object* v_t_3514_, lean_object* v_incomplete_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3514_, v_incomplete_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_TakeResult_incomplete_elim(lean_object* v_motive_3517_, lean_object* v_t_3518_, lean_object* v_h_3519_, lean_object* v_incomplete_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Std_Http_Protocol_H1_TakeResult_ctorElim___redArg(v_t_3518_, v_incomplete_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkPartial(lean_object* v_limits_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Std_Http_Protocol_H1_parseChunkSize(v_limits_3522_, v_a_3523_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_res_3525_; lean_object* v_pos_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3566_; 
v_res_3525_ = lean_ctor_get(v___x_3524_, 1);
v_pos_3526_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3528_ = v___x_3524_;
v_isShared_3529_ = v_isSharedCheck_3566_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_res_3525_);
lean_inc(v_pos_3526_);
lean_dec(v___x_3524_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3566_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_fst_3530_; lean_object* v_snd_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3565_; 
v_fst_3530_ = lean_ctor_get(v_res_3525_, 0);
v_snd_3531_ = lean_ctor_get(v_res_3525_, 1);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_res_3525_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3533_ = v_res_3525_;
v_isShared_3534_ = v_isSharedCheck_3565_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_snd_3531_);
lean_inc(v_fst_3530_);
lean_dec(v_res_3525_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3565_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3535_ = lean_unsigned_to_nat(0u);
v___x_3536_ = lean_nat_dec_eq(v_fst_3530_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_del_object(v___x_3528_);
v___x_3537_ = l_Std_Internal_Parsec_ByteArray_take(v_fst_3530_, v_pos_3526_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_pos_3538_; lean_object* v_res_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3551_; 
v_pos_3538_ = lean_ctor_get(v___x_3537_, 0);
v_res_3539_ = lean_ctor_get(v___x_3537_, 1);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3541_ = v___x_3537_;
v_isShared_3542_ = v_isSharedCheck_3551_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_res_3539_);
lean_inc(v_pos_3538_);
lean_dec(v___x_3537_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3551_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 1, v_res_3539_);
lean_ctor_set(v___x_3533_, 0, v_snd_3531_);
v___x_3544_ = v___x_3533_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_snd_3531_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_res_3539_);
v___x_3544_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v_fst_3530_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 1, v___x_3546_);
v___x_3548_ = v___x_3541_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_pos_3538_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
lean_object* v_pos_3552_; lean_object* v_err_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_del_object(v___x_3533_);
lean_dec(v_snd_3531_);
lean_dec(v_fst_3530_);
v_pos_3552_ = lean_ctor_get(v___x_3537_, 0);
v_err_3553_ = lean_ctor_get(v___x_3537_, 1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3537_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_err_3553_);
lean_inc(v_pos_3552_);
lean_dec(v___x_3537_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_pos_3552_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_err_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v___x_3561_; lean_object* v___x_3563_; 
lean_del_object(v___x_3533_);
lean_dec(v_snd_3531_);
lean_dec(v_fst_3530_);
v___x_3561_ = lean_box(0);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v___x_3561_);
v___x_3563_ = v___x_3528_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_pos_3526_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
else
{
lean_object* v_pos_3567_; lean_object* v_err_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
v_pos_3567_ = lean_ctor_get(v___x_3524_, 0);
v_err_3568_ = lean_ctor_get(v___x_3524_, 1);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3524_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_err_3568_);
lean_inc(v_pos_3567_);
lean_dec(v___x_3524_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_pos_3567_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_err_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData(lean_object* v_size_3576_, lean_object* v_it_3577_){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; uint8_t v___x_3580_; 
v___x_3578_ = l_ByteArray_Iterator_remainingBytes(v_it_3577_);
v___x_3579_ = lean_unsigned_to_nat(0u);
v___x_3580_ = lean_nat_dec_eq(v___x_3578_, v___x_3579_);
if (v___x_3580_ == 0)
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_nat_dec_lt(v___x_3578_, v_size_3576_);
if (v___x_3581_ == 0)
{
lean_object* v_array_3582_; lean_object* v_idx_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v___x_3578_);
v_array_3582_ = lean_ctor_get(v_it_3577_, 0);
v_idx_3583_ = lean_ctor_get(v_it_3577_, 1);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_it_3577_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3585_ = v_it_3577_;
v_isShared_3586_ = v_isSharedCheck_3602_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_idx_3583_);
lean_inc(v_array_3582_);
lean_dec(v_it_3577_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3602_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3587_ = lean_nat_add(v_idx_3583_, v_size_3576_);
lean_inc(v___x_3587_);
lean_inc_ref(v_array_3582_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 1, v___x_3587_);
v___x_3589_ = v___x_3585_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_array_3582_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v_lower_3591_; lean_object* v_upper_3592_; lean_object* v___x_3596_; lean_object* v___y_3598_; uint8_t v___x_3600_; 
v___x_3596_ = lean_byte_array_size(v_array_3582_);
v___x_3600_ = lean_nat_dec_le(v_idx_3583_, v___x_3579_);
if (v___x_3600_ == 0)
{
v___y_3598_ = v_idx_3583_;
goto v___jp_3597_;
}
else
{
lean_dec(v_idx_3583_);
v___y_3598_ = v___x_3579_;
goto v___jp_3597_;
}
v___jp_3590_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = l_ByteArray_toByteSlice(v_array_3582_, v_lower_3591_, v_upper_3592_);
v___x_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3589_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
return v___x_3595_;
}
v___jp_3597_:
{
uint8_t v___x_3599_; 
v___x_3599_ = lean_nat_dec_le(v___x_3587_, v___x_3596_);
if (v___x_3599_ == 0)
{
lean_dec(v___x_3587_);
v_lower_3591_ = v___y_3598_;
v_upper_3592_ = v___x_3596_;
goto v___jp_3590_;
}
else
{
v_lower_3591_ = v___y_3598_;
v_upper_3592_ = v___x_3587_;
goto v___jp_3590_;
}
}
}
}
}
else
{
lean_object* v_array_3603_; lean_object* v_idx_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3624_; 
v_array_3603_ = lean_ctor_get(v_it_3577_, 0);
v_idx_3604_ = lean_ctor_get(v_it_3577_, 1);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_it_3577_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3606_ = v_it_3577_;
v_isShared_3607_ = v_isSharedCheck_3624_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_idx_3604_);
lean_inc(v_array_3603_);
lean_dec(v_it_3577_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3624_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = lean_nat_add(v_idx_3604_, v___x_3578_);
lean_inc(v___x_3608_);
lean_inc_ref(v_array_3603_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 1, v___x_3608_);
v___x_3610_ = v___x_3606_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_array_3603_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v_lower_3612_; lean_object* v_upper_3613_; lean_object* v___x_3618_; lean_object* v___y_3620_; uint8_t v___x_3622_; 
v___x_3618_ = lean_byte_array_size(v_array_3603_);
v___x_3622_ = lean_nat_dec_le(v_idx_3604_, v___x_3579_);
if (v___x_3622_ == 0)
{
v___y_3620_ = v_idx_3604_;
goto v___jp_3619_;
}
else
{
lean_dec(v_idx_3604_);
v___y_3620_ = v___x_3579_;
goto v___jp_3619_;
}
v___jp_3611_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3614_ = l_ByteArray_toByteSlice(v_array_3603_, v_lower_3612_, v_upper_3613_);
v___x_3615_ = lean_nat_sub(v_size_3576_, v___x_3578_);
lean_dec(v___x_3578_);
v___x_3616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3610_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
return v___x_3617_;
}
v___jp_3619_:
{
uint8_t v___x_3621_; 
v___x_3621_ = lean_nat_dec_le(v___x_3608_, v___x_3618_);
if (v___x_3621_ == 0)
{
lean_dec(v___x_3608_);
v_lower_3612_ = v___y_3620_;
v_upper_3613_ = v___x_3618_;
goto v___jp_3611_;
}
else
{
v_lower_3612_ = v___y_3620_;
v_upper_3613_ = v___x_3608_;
goto v___jp_3611_;
}
}
}
}
}
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_dec(v___x_3578_);
v___x_3625_ = lean_box(0);
v___x_3626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3626_, 0, v_it_3577_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
return v___x_3626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseFixedSizeData___boxed(lean_object* v_size_3627_, lean_object* v_it_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3627_, v_it_3628_);
lean_dec(v_size_3627_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData(lean_object* v_size_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Std_Http_Protocol_H1_parseFixedSizeData(v_size_3630_, v_a_3631_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_res_3633_; 
v_res_3633_ = lean_ctor_get(v___x_3632_, 1);
if (lean_obj_tag(v_res_3633_) == 0)
{
lean_object* v_pos_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_inc_ref(v_res_3633_);
v_pos_3634_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_pos_3634_);
lean_dec_ref_known(v___x_3632_, 2);
v___x_3635_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3636_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3635_, v_pos_3634_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_pos_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
v_pos_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3644_ == 0)
{
lean_object* v_unused_3645_; 
v_unused_3645_ = lean_ctor_get(v___x_3636_, 1);
lean_dec(v_unused_3645_);
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_pos_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 1, v_res_3633_);
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_pos_3637_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_res_3633_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
else
{
lean_object* v_pos_3646_; lean_object* v_err_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec_ref_known(v_res_3633_, 1);
v_pos_3646_ = lean_ctor_get(v___x_3636_, 0);
v_err_3647_ = lean_ctor_get(v___x_3636_, 1);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3636_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_err_3647_);
lean_inc(v_pos_3646_);
lean_dec(v___x_3636_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_pos_3646_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_err_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
else
{
return v___x_3632_;
}
}
else
{
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseChunkSizedData___boxed(lean_object* v_size_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Std_Http_Protocol_H1_parseChunkSizedData(v_size_3655_, v_a_3656_);
lean_dec(v_size_3655_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(lean_object* v_s_3658_, lean_object* v_p_3659_){
_start:
{
uint32_t v___y_3661_; lean_object* v___x_3666_; uint8_t v_decide_3667_; 
v___x_3666_ = lean_string_utf8_byte_size(v_s_3658_);
v_decide_3667_ = lean_nat_dec_eq(v_p_3659_, v___x_3666_);
if (v_decide_3667_ == 0)
{
uint32_t v___x_3668_; uint32_t v___x_3669_; uint8_t v___x_3670_; 
v___x_3668_ = lean_string_utf8_get_fast(v_s_3658_, v_p_3659_);
v___x_3669_ = 65;
v___x_3670_ = lean_uint32_dec_le(v___x_3669_, v___x_3668_);
if (v___x_3670_ == 0)
{
v___y_3661_ = v___x_3668_;
goto v___jp_3660_;
}
else
{
uint32_t v___x_3671_; uint8_t v___x_3672_; 
v___x_3671_ = 90;
v___x_3672_ = lean_uint32_dec_le(v___x_3668_, v___x_3671_);
if (v___x_3672_ == 0)
{
v___y_3661_ = v___x_3668_;
goto v___jp_3660_;
}
else
{
uint32_t v___x_3673_; uint32_t v___x_3674_; 
v___x_3673_ = 32;
v___x_3674_ = lean_uint32_add(v___x_3668_, v___x_3673_);
v___y_3661_ = v___x_3674_;
goto v___jp_3660_;
}
}
}
else
{
lean_dec(v_p_3659_);
return v_s_3658_;
}
v___jp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_inc(v_p_3659_);
v___x_3662_ = lean_string_utf8_set(v_s_3658_, v_p_3659_, v___y_3661_);
v___x_3663_ = l_Char_utf8Size(v___y_3661_);
v___x_3664_ = lean_nat_add(v_p_3659_, v___x_3663_);
lean_dec(v___x_3663_);
lean_dec(v_p_3659_);
v_s_3658_ = v___x_3662_;
v_p_3659_ = v___x_3664_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(lean_object* v_name_3687_){
_start:
{
lean_object* v___x_3688_; lean_object* v_n_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3688_ = lean_unsigned_to_nat(0u);
v_n_3689_ = l_String_mapAux___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField_spec__0(v_name_3687_, v___x_3688_);
v___x_3690_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__0));
v___x_3691_ = lean_string_dec_eq(v_n_3689_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3692_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__1));
v___x_3693_ = lean_string_dec_eq(v_n_3689_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3694_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__2));
v___x_3695_ = lean_string_dec_eq(v_n_3689_, v___x_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; uint8_t v___x_3697_; 
v___x_3696_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__3));
v___x_3697_ = lean_string_dec_eq(v_n_3689_, v___x_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3698_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__4));
v___x_3699_ = lean_string_dec_eq(v_n_3689_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; uint8_t v___x_3701_; 
v___x_3700_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__5));
v___x_3701_ = lean_string_dec_eq(v_n_3689_, v___x_3700_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; uint8_t v___x_3703_; 
v___x_3702_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__6));
v___x_3703_ = lean_string_dec_eq(v_n_3689_, v___x_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; uint8_t v___x_3705_; 
v___x_3704_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__7));
v___x_3705_ = lean_string_dec_eq(v_n_3689_, v___x_3704_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; uint8_t v___x_3707_; 
v___x_3706_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__8));
v___x_3707_ = lean_string_dec_eq(v_n_3689_, v___x_3706_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___x_3708_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__9));
v___x_3709_ = lean_string_dec_eq(v_n_3689_, v___x_3708_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__10));
v___x_3711_ = lean_string_dec_eq(v_n_3689_, v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3712_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___closed__11));
v___x_3713_ = lean_string_dec_eq(v_n_3689_, v___x_3712_);
lean_dec_ref(v_n_3689_);
return v___x_3713_;
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3711_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3709_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3707_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3705_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3703_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3701_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3699_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3697_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3695_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3693_;
}
}
else
{
lean_dec_ref(v_n_3689_);
return v___x_3691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField___boxed(lean_object* v_name_3714_){
_start:
{
uint8_t v_res_3715_; lean_object* v_r_3716_; 
v_res_3715_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_name_3714_);
v_r_3716_ = lean_box(v_res_3715_);
return v_r_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(lean_object* v_limits_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Std_Http_Protocol_H1_parseSingleHeader(v_limits_3718_, v_a_3719_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_res_3721_; 
v_res_3721_ = lean_ctor_get(v___x_3720_, 1);
lean_inc(v_res_3721_);
if (lean_obj_tag(v_res_3721_) == 1)
{
lean_object* v_val_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3743_; 
v_val_3722_ = lean_ctor_get(v_res_3721_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_res_3721_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3724_ = v_res_3721_;
v_isShared_3725_ = v_isSharedCheck_3743_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_val_3722_);
lean_dec(v_res_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3743_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v_pos_3726_; lean_object* v_fst_3727_; uint8_t v___x_3728_; 
v_pos_3726_ = lean_ctor_get(v___x_3720_, 0);
v_fst_3727_ = lean_ctor_get(v_val_3722_, 0);
lean_inc_n(v_fst_3727_, 2);
lean_dec(v_val_3722_);
v___x_3728_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isForbiddenTrailerField(v_fst_3727_);
if (v___x_3728_ == 0)
{
lean_dec(v_fst_3727_);
lean_del_object(v___x_3724_);
return v___x_3720_;
}
else
{
lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3740_; 
lean_inc(v_pos_3726_);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; 
v_unused_3741_ = lean_ctor_get(v___x_3720_, 1);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v___x_3720_, 0);
lean_dec(v_unused_3742_);
v___x_3730_ = v___x_3720_;
v_isShared_3731_ = v_isSharedCheck_3740_;
goto v_resetjp_3729_;
}
else
{
lean_dec(v___x_3720_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3740_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
v___x_3732_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___closed__0));
v___x_3733_ = lean_string_append(v___x_3732_, v_fst_3727_);
lean_dec(v_fst_3727_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3733_);
v___x_3735_ = v___x_3724_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3737_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set_tag(v___x_3730_, 1);
lean_ctor_set(v___x_3730_, 1, v___x_3735_);
v___x_3737_ = v___x_3730_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_pos_3726_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___x_3735_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
}
else
{
lean_dec(v_res_3721_);
return v___x_3720_;
}
}
else
{
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed(lean_object* v_limits_3744_, lean_object* v_a_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader(v_limits_3744_, v_a_3745_);
lean_dec_ref(v_limits_3744_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseTrailers(lean_object* v_limits_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v_maxTrailerHeaders_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v_maxTrailerHeaders_3749_ = lean_ctor_get(v_limits_3747_, 17);
lean_inc(v_maxTrailerHeaders_3749_);
v___x_3750_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_3750_, 0, v_limits_3747_);
v___x_3751_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_3750_, v_maxTrailerHeaders_3749_, v_a_3748_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_pos_3752_; lean_object* v_res_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_pos_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_pos_3752_);
v_res_3753_ = lean_ctor_get(v___x_3751_, 1);
lean_inc(v_res_3753_);
lean_dec_ref_known(v___x_3751_, 2);
v___x_3754_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3755_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3754_, v_pos_3752_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_pos_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
v_pos_3756_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; 
v_unused_3764_ = lean_ctor_get(v___x_3755_, 1);
lean_dec(v_unused_3764_);
v___x_3758_ = v___x_3755_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_pos_3756_);
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 1, v_res_3753_);
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_pos_3756_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_res_3753_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
else
{
lean_object* v_pos_3765_; lean_object* v_err_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec(v_res_3753_);
v_pos_3765_ = lean_ctor_get(v___x_3755_, 0);
v_err_3766_ = lean_ctor_get(v___x_3755_, 1);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3755_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_err_3766_);
lean_inc(v_pos_3765_);
lean_dec(v___x_3755_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_pos_3765_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_err_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
else
{
return v___x_3751_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(uint8_t v_c_3774_){
_start:
{
uint32_t v___x_3775_; uint32_t v___x_3781_; uint8_t v___x_3782_; 
v___x_3775_ = lean_uint8_to_uint32(v_c_3774_);
v___x_3781_ = 33;
v___x_3782_ = lean_uint32_dec_le(v___x_3781_, v___x_3775_);
if (v___x_3782_ == 0)
{
goto v___jp_3776_;
}
else
{
uint32_t v___x_3783_; uint8_t v___x_3784_; 
v___x_3783_ = 126;
v___x_3784_ = lean_uint32_dec_le(v___x_3775_, v___x_3783_);
if (v___x_3784_ == 0)
{
goto v___jp_3776_;
}
else
{
return v___x_3784_;
}
}
v___jp_3776_:
{
uint32_t v___x_3777_; uint8_t v___x_3778_; 
v___x_3777_ = 32;
v___x_3778_ = lean_uint32_dec_eq(v___x_3775_, v___x_3777_);
if (v___x_3778_ == 0)
{
uint32_t v___x_3779_; uint8_t v___x_3780_; 
v___x_3779_ = 9;
v___x_3780_ = lean_uint32_dec_eq(v___x_3775_, v___x_3779_);
return v___x_3780_;
}
else
{
return v___x_3778_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte___boxed(lean_object* v_c_3785_){
_start:
{
uint8_t v_c_boxed_3786_; uint8_t v_res_3787_; lean_object* v_r_3788_; 
v_c_boxed_3786_ = lean_unbox(v_c_3785_);
v_res_3787_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_isReasonPhraseByte(v_c_boxed_3786_);
v_r_3788_ = lean_box(v_res_3787_);
return v_r_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(lean_object* v_limits_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v_maxReasonPhraseLength_3791_; lean_object* v___f_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v_snd_3795_; lean_object* v_snd_3796_; uint8_t v___x_3797_; 
v_maxReasonPhraseLength_3791_ = lean_ctor_get(v_limits_3789_, 16);
v___f_3792_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseFieldLine___closed__1));
v___x_3793_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_3790_);
v___x_3794_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_scanWhileUpTo(v___f_3792_, v_maxReasonPhraseLength_3791_, v___x_3793_, v_a_3790_);
v_snd_3795_ = lean_ctor_get(v___x_3794_, 1);
lean_inc(v_snd_3795_);
v_snd_3796_ = lean_ctor_get(v_snd_3795_, 1);
v___x_3797_ = lean_unbox(v_snd_3796_);
if (v___x_3797_ == 0)
{
lean_object* v_fst_3798_; lean_object* v_fst_3799_; lean_object* v_array_3800_; lean_object* v_idx_3801_; lean_object* v_lower_3803_; lean_object* v_upper_3804_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___y_3816_; uint8_t v___x_3818_; 
v_fst_3798_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_fst_3798_);
lean_dec_ref(v___x_3794_);
v_fst_3799_ = lean_ctor_get(v_snd_3795_, 0);
lean_inc(v_fst_3799_);
lean_dec(v_snd_3795_);
v_array_3800_ = lean_ctor_get(v_a_3790_, 0);
lean_inc_ref(v_array_3800_);
v_idx_3801_ = lean_ctor_get(v_a_3790_, 1);
lean_inc(v_idx_3801_);
lean_dec_ref(v_a_3790_);
v___x_3813_ = lean_nat_add(v_idx_3801_, v_fst_3798_);
lean_dec(v_fst_3798_);
v___x_3814_ = lean_byte_array_size(v_array_3800_);
v___x_3818_ = lean_nat_dec_le(v_idx_3801_, v___x_3793_);
if (v___x_3818_ == 0)
{
v___y_3816_ = v_idx_3801_;
goto v___jp_3815_;
}
else
{
lean_dec(v_idx_3801_);
v___y_3816_ = v___x_3793_;
goto v___jp_3815_;
}
v___jp_3802_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = l_ByteArray_toByteSlice(v_array_3800_, v_lower_3803_, v_upper_3804_);
v___x_3806_ = l_ByteSlice_toByteArray(v___x_3805_);
v___x_3807_ = lean_string_validate_utf8(v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_dec_ref(v___x_3806_);
v___x_3808_ = lean_box(0);
v___x_3809_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3808_, v_fst_3799_);
return v___x_3809_;
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = lean_string_from_utf8_unchecked(v___x_3806_);
v___x_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
v___x_3812_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_liftOption___redArg(v___x_3811_, v_fst_3799_);
lean_dec_ref_known(v___x_3811_, 1);
return v___x_3812_;
}
}
v___jp_3815_:
{
uint8_t v___x_3817_; 
v___x_3817_ = lean_nat_dec_le(v___x_3813_, v___x_3814_);
if (v___x_3817_ == 0)
{
lean_dec(v___x_3813_);
v_lower_3803_ = v___y_3816_;
v_upper_3804_ = v___x_3814_;
goto v___jp_3802_;
}
else
{
v_lower_3803_ = v___y_3816_;
v_upper_3804_ = v___x_3813_;
goto v___jp_3802_;
}
}
}
else
{
lean_object* v_fst_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v___x_3794_);
lean_dec_ref(v_a_3790_);
v_fst_3819_ = lean_ctor_get(v_snd_3795_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_snd_3795_);
if (v_isSharedCheck_3827_ == 0)
{
lean_object* v_unused_3828_; 
v_unused_3828_ = lean_ctor_get(v_snd_3795_, 1);
lean_dec(v_unused_3828_);
v___x_3821_ = v_snd_3795_;
v_isShared_3822_ = v_isSharedCheck_3827_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_fst_3819_);
lean_dec(v_snd_3795_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3827_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3823_ = lean_box(0);
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 1);
lean_ctor_set(v___x_3821_, 1, v___x_3823_);
v___x_3825_ = v___x_3821_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_fst_3819_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase___boxed(lean_object* v_limits_3829_, lean_object* v_a_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3829_, v_a_3830_);
lean_dec_ref(v_limits_3829_);
return v_res_3831_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(lean_object* v_x_3832_){
_start:
{
if (lean_obj_tag(v_x_3832_) == 0)
{
uint8_t v___x_3833_; 
v___x_3833_ = 1;
return v___x_3833_;
}
else
{
lean_object* v_head_3834_; lean_object* v_tail_3835_; uint32_t v___x_3836_; uint32_t v___x_3837_; uint8_t v___x_3838_; 
v_head_3834_ = lean_ctor_get(v_x_3832_, 0);
v_tail_3835_ = lean_ctor_get(v_x_3832_, 1);
v___x_3836_ = 9;
v___x_3837_ = lean_unbox_uint32(v_head_3834_);
v___x_3838_ = lean_uint32_dec_eq(v___x_3837_, v___x_3836_);
if (v___x_3838_ == 0)
{
uint32_t v___x_3839_; uint32_t v___x_3840_; uint8_t v___x_3841_; 
v___x_3839_ = 32;
v___x_3840_ = lean_unbox_uint32(v_head_3834_);
v___x_3841_ = lean_uint32_dec_eq(v___x_3840_, v___x_3839_);
if (v___x_3841_ == 0)
{
uint32_t v___x_3842_; uint32_t v___x_3843_; uint8_t v___x_3844_; 
v___x_3842_ = 33;
v___x_3843_ = lean_unbox_uint32(v_head_3834_);
v___x_3844_ = lean_uint32_dec_le(v___x_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
return v___x_3844_;
}
else
{
uint32_t v___x_3845_; uint32_t v___x_3846_; uint8_t v___x_3847_; 
v___x_3845_ = 126;
v___x_3846_ = lean_unbox_uint32(v_head_3834_);
v___x_3847_ = lean_uint32_dec_le(v___x_3846_, v___x_3845_);
if (v___x_3847_ == 0)
{
return v___x_3847_;
}
else
{
v_x_3832_ = v_tail_3835_;
goto _start;
}
}
}
else
{
v_x_3832_ = v_tail_3835_;
goto _start;
}
}
else
{
v_x_3832_ = v_tail_3835_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0___boxed(lean_object* v_x_3851_){
_start:
{
uint8_t v_res_3852_; lean_object* v_r_3853_; 
v_res_3852_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v_x_3851_);
lean_dec(v_x_3851_);
v_r_3853_ = lean_box(v_res_3852_);
return v_r_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(lean_object* v_limits_3857_, lean_object* v_a_3858_){
_start:
{
lean_object* v___y_3860_; lean_object* v_array_3866_; lean_object* v_idx_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v_array_3866_ = lean_ctor_get(v_a_3858_, 0);
v_idx_3867_ = lean_ctor_get(v_a_3858_, 1);
v___x_3868_ = lean_byte_array_size(v_array_3866_);
v___x_3869_ = lean_nat_dec_lt(v_idx_3867_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = lean_box(0);
v___x_3871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3871_, 0, v_a_3858_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
return v___x_3871_;
}
else
{
uint8_t v_c_3872_; uint8_t v___x_3873_; uint8_t v___x_3874_; 
v_c_3872_ = lean_byte_array_fget(v_array_3866_, v_idx_3867_);
v___x_3873_ = 48;
v___x_3874_ = lean_uint8_dec_le(v___x_3873_, v_c_3872_);
if (v___x_3874_ == 0)
{
goto v___jp_3863_;
}
else
{
uint8_t v___x_3875_; uint8_t v___x_3876_; 
v___x_3875_ = 57;
v___x_3876_ = lean_uint8_dec_le(v_c_3872_, v___x_3875_);
if (v___x_3876_ == 0)
{
goto v___jp_3863_;
}
else
{
lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3969_; 
lean_inc(v_idx_3867_);
lean_inc_ref(v_array_3866_);
v_isSharedCheck_3969_ = !lean_is_exclusive(v_a_3858_);
if (v_isSharedCheck_3969_ == 0)
{
lean_object* v_unused_3970_; lean_object* v_unused_3971_; 
v_unused_3970_ = lean_ctor_get(v_a_3858_, 1);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_a_3858_, 0);
lean_dec(v_unused_3971_);
v___x_3878_ = v_a_3858_;
v_isShared_3879_ = v_isSharedCheck_3969_;
goto v_resetjp_3877_;
}
else
{
lean_dec(v_a_3858_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3969_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v_it_x27_3883_; 
v___x_3880_ = lean_unsigned_to_nat(1u);
v___x_3881_ = lean_nat_add(v_idx_3867_, v___x_3880_);
lean_dec(v_idx_3867_);
lean_inc(v___x_3881_);
lean_inc_ref(v_array_3866_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v___x_3881_);
v_it_x27_3883_ = v___x_3878_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_array_3866_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v___x_3881_);
v_it_x27_3883_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
uint8_t v___x_3887_; 
v___x_3887_ = lean_nat_dec_lt(v___x_3881_, v___x_3868_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
lean_dec(v___x_3881_);
lean_dec_ref(v_array_3866_);
v___x_3888_ = lean_box(0);
v___x_3889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3889_, 0, v_it_x27_3883_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
return v___x_3889_;
}
else
{
uint8_t v_c_3890_; uint8_t v___x_3891_; 
v_c_3890_ = lean_byte_array_fget(v_array_3866_, v___x_3881_);
v___x_3891_ = lean_uint8_dec_le(v___x_3873_, v_c_3890_);
if (v___x_3891_ == 0)
{
lean_dec(v___x_3881_);
lean_dec_ref(v_array_3866_);
goto v___jp_3884_;
}
else
{
uint8_t v___x_3892_; 
v___x_3892_ = lean_uint8_dec_le(v_c_3890_, v___x_3875_);
if (v___x_3892_ == 0)
{
lean_dec(v___x_3881_);
lean_dec_ref(v_array_3866_);
goto v___jp_3884_;
}
else
{
lean_object* v___x_3893_; lean_object* v_it_x27_3894_; uint8_t v___x_3898_; 
lean_dec_ref(v_it_x27_3883_);
v___x_3893_ = lean_nat_add(v___x_3881_, v___x_3880_);
lean_dec(v___x_3881_);
lean_inc(v___x_3893_);
lean_inc_ref(v_array_3866_);
v_it_x27_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3894_, 0, v_array_3866_);
lean_ctor_set(v_it_x27_3894_, 1, v___x_3893_);
v___x_3898_ = lean_nat_dec_lt(v___x_3893_, v___x_3868_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
lean_dec(v___x_3893_);
lean_dec_ref(v_array_3866_);
v___x_3899_ = lean_box(0);
v___x_3900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3900_, 0, v_it_x27_3894_);
lean_ctor_set(v___x_3900_, 1, v___x_3899_);
return v___x_3900_;
}
else
{
uint8_t v_c_3901_; uint8_t v___x_3902_; 
v_c_3901_ = lean_byte_array_fget(v_array_3866_, v___x_3893_);
v___x_3902_ = lean_uint8_dec_le(v___x_3873_, v_c_3901_);
if (v___x_3902_ == 0)
{
lean_dec(v___x_3893_);
lean_dec_ref(v_array_3866_);
goto v___jp_3895_;
}
else
{
uint8_t v___x_3903_; 
v___x_3903_ = lean_uint8_dec_le(v_c_3901_, v___x_3875_);
if (v___x_3903_ == 0)
{
lean_dec(v___x_3893_);
lean_dec_ref(v_array_3866_);
goto v___jp_3895_;
}
else
{
lean_object* v___x_3904_; lean_object* v_it_x27_3905_; uint8_t v___x_3906_; 
lean_dec_ref_known(v_it_x27_3894_, 2);
v___x_3904_ = lean_nat_add(v___x_3893_, v___x_3880_);
lean_dec(v___x_3893_);
lean_inc(v___x_3904_);
lean_inc_ref(v_array_3866_);
v_it_x27_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3905_, 0, v_array_3866_);
lean_ctor_set(v_it_x27_3905_, 1, v___x_3904_);
v___x_3906_ = lean_nat_dec_lt(v___x_3904_, v___x_3868_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_dec(v___x_3904_);
lean_dec_ref(v_array_3866_);
v___x_3907_ = lean_box(0);
v___x_3908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3908_, 0, v_it_x27_3905_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
return v___x_3908_;
}
else
{
uint8_t v___x_3909_; uint8_t v_got_3910_; uint8_t v___x_3911_; 
v___x_3909_ = 32;
v_got_3910_ = lean_byte_array_fget(v_array_3866_, v___x_3904_);
v___x_3911_ = lean_uint8_dec_eq(v_got_3910_, v___x_3909_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
lean_dec(v___x_3904_);
lean_dec_ref(v_array_3866_);
v___x_3912_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
v___x_3913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3913_, 0, v_it_x27_3905_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
return v___x_3913_;
}
else
{
lean_object* v___x_3914_; uint32_t v___x_3915_; uint32_t v___x_3916_; uint32_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v_pos_3931_; lean_object* v_res_3932_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
lean_dec_ref_known(v_it_x27_3905_, 2);
v___x_3914_ = lean_unsigned_to_nat(48u);
v___x_3915_ = lean_uint8_to_uint32(v_c_3872_);
v___x_3916_ = lean_uint8_to_uint32(v_c_3890_);
v___x_3917_ = lean_uint8_to_uint32(v_c_3901_);
v___x_3918_ = lean_uint32_to_nat(v___x_3915_);
v___x_3919_ = lean_nat_sub(v___x_3918_, v___x_3914_);
lean_dec(v___x_3918_);
v___x_3920_ = lean_unsigned_to_nat(100u);
v___x_3921_ = lean_nat_mul(v___x_3919_, v___x_3920_);
lean_dec(v___x_3919_);
v___x_3922_ = lean_uint32_to_nat(v___x_3916_);
v___x_3923_ = lean_nat_sub(v___x_3922_, v___x_3914_);
lean_dec(v___x_3922_);
v___x_3924_ = lean_unsigned_to_nat(10u);
v___x_3925_ = lean_nat_mul(v___x_3923_, v___x_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_nat_add(v___x_3921_, v___x_3925_);
lean_dec(v___x_3925_);
lean_dec(v___x_3921_);
v___x_3927_ = lean_uint32_to_nat(v___x_3917_);
v___x_3928_ = lean_nat_sub(v___x_3927_, v___x_3914_);
lean_dec(v___x_3927_);
v___x_3929_ = lean_nat_add(v___x_3926_, v___x_3928_);
lean_dec(v___x_3928_);
lean_dec(v___x_3926_);
v___x_3940_ = lean_nat_add(v___x_3904_, v___x_3880_);
lean_dec(v___x_3904_);
v___x_3941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3941_, 0, v_array_3866_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseReasonPhrase(v_limits_3857_, v___x_3941_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_pos_3943_; lean_object* v_res_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_pos_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_pos_3943_);
v_res_3944_ = lean_ctor_get(v___x_3942_, 1);
lean_inc(v_res_3944_);
lean_dec_ref_known(v___x_3942_, 2);
v___x_3945_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_3946_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_3945_, v_pos_3943_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_pos_3947_; 
v_pos_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_pos_3947_);
lean_dec_ref_known(v___x_3946_, 2);
v_pos_3931_ = v_pos_3947_;
v_res_3932_ = v_res_3944_;
goto v___jp_3930_;
}
else
{
lean_object* v_pos_3948_; lean_object* v_err_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec(v_res_3944_);
lean_dec(v___x_3929_);
v_pos_3948_ = lean_ctor_get(v___x_3946_, 0);
v_err_3949_ = lean_ctor_get(v___x_3946_, 1);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3946_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_err_3949_);
lean_inc(v_pos_3948_);
lean_dec(v___x_3946_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_pos_3948_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_err_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_pos_3957_; lean_object* v_res_3958_; 
v_pos_3957_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_pos_3957_);
v_res_3958_ = lean_ctor_get(v___x_3942_, 1);
lean_inc(v_res_3958_);
lean_dec_ref_known(v___x_3942_, 2);
v_pos_3931_ = v_pos_3957_;
v_res_3932_ = v_res_3958_;
goto v___jp_3930_;
}
else
{
lean_object* v_pos_3959_; lean_object* v_err_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v___x_3929_);
v_pos_3959_ = lean_ctor_get(v___x_3942_, 0);
v_err_3960_ = lean_ctor_get(v___x_3942_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3942_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_err_3960_);
lean_inc(v_pos_3959_);
lean_dec(v___x_3942_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_pos_3959_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_err_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
v___jp_3930_:
{
lean_object* v___x_3933_; uint8_t v___x_3934_; 
lean_inc_ref(v_res_3932_);
v___x_3933_ = l_String_toListImpl(v_res_3932_);
v___x_3934_ = l_List_all___at___00__private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode_spec__0(v___x_3933_);
lean_dec(v___x_3933_);
if (v___x_3934_ == 0)
{
lean_dec_ref(v_res_3932_);
lean_dec(v___x_3929_);
v___y_3860_ = v_pos_3931_;
goto v___jp_3859_;
}
else
{
lean_object* v___x_3935_; uint16_t v___x_3936_; lean_object* v___x_3937_; 
v___x_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3935_, 0, v_res_3932_);
v___x_3936_ = lean_uint16_of_nat(v___x_3929_);
lean_dec(v___x_3929_);
v___x_3937_ = l_Std_Http_Status_ofCode(v___x_3935_, v___x_3936_);
if (lean_obj_tag(v___x_3937_) == 1)
{
lean_object* v_val_3938_; lean_object* v___x_3939_; 
v_val_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_val_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v_pos_3931_);
lean_ctor_set(v___x_3939_, 1, v_val_3938_);
return v___x_3939_;
}
else
{
lean_dec(v___x_3937_);
v___y_3860_ = v_pos_3931_;
goto v___jp_3859_;
}
}
}
}
}
}
}
}
v___jp_3895_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_it_x27_3894_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
return v___x_3897_;
}
}
}
}
v___jp_3884_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3886_, 0, v_it_x27_3883_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
return v___x_3886_;
}
}
}
}
}
}
v___jp_3859_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___closed__1));
v___x_3862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___y_3860_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
return v___x_3862_;
}
v___jp_3863_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber___closed__3));
v___x_3865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3865_, 0, v_a_3858_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
return v___x_3865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode___boxed(lean_object* v_limits_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3972_, v_a_3973_);
lean_dec_ref(v_limits_3972_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine(lean_object* v_limits_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v___y_3978_; lean_object* v___y_3982_; uint8_t v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v_pos_3993_; lean_object* v_res_3994_; lean_object* v___x_4022_; 
v___x_4022_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_3976_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_pos_4023_; lean_object* v_res_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4054_; 
v_pos_4023_ = lean_ctor_get(v___x_4022_, 0);
v_res_4024_ = lean_ctor_get(v___x_4022_, 1);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4026_ = v___x_4022_;
v_isShared_4027_ = v_isSharedCheck_4054_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_res_4024_);
lean_inc(v_pos_4023_);
lean_dec(v___x_4022_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4054_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v_array_4028_; lean_object* v_idx_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; 
v_array_4028_ = lean_ctor_get(v_pos_4023_, 0);
v_idx_4029_ = lean_ctor_get(v_pos_4023_, 1);
v___x_4030_ = lean_byte_array_size(v_array_4028_);
v___x_4031_ = lean_nat_dec_lt(v_idx_4029_, v___x_4030_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4034_; 
lean_dec(v_res_4024_);
v___x_4032_ = lean_box(0);
if (v_isShared_4027_ == 0)
{
lean_ctor_set_tag(v___x_4026_, 1);
lean_ctor_set(v___x_4026_, 1, v___x_4032_);
v___x_4034_ = v___x_4026_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_pos_4023_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
else
{
uint8_t v___x_4036_; uint8_t v_got_4037_; uint8_t v___x_4038_; 
v___x_4036_ = 32;
v_got_4037_ = lean_byte_array_fget(v_array_4028_, v_idx_4029_);
v___x_4038_ = lean_uint8_dec_eq(v_got_4037_, v___x_4036_);
if (v___x_4038_ == 0)
{
lean_object* v___x_4039_; lean_object* v___x_4041_; 
lean_dec(v_res_4024_);
v___x_4039_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_4027_ == 0)
{
lean_ctor_set_tag(v___x_4026_, 1);
lean_ctor_set(v___x_4026_, 1, v___x_4039_);
v___x_4041_ = v___x_4026_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_pos_4023_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v___x_4039_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
else
{
lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4051_; 
lean_inc(v_idx_4029_);
lean_inc_ref(v_array_4028_);
lean_del_object(v___x_4026_);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_pos_4023_);
if (v_isSharedCheck_4051_ == 0)
{
lean_object* v_unused_4052_; lean_object* v_unused_4053_; 
v_unused_4052_ = lean_ctor_get(v_pos_4023_, 1);
lean_dec(v_unused_4052_);
v_unused_4053_ = lean_ctor_get(v_pos_4023_, 0);
lean_dec(v_unused_4053_);
v___x_4044_ = v_pos_4023_;
v_isShared_4045_ = v_isSharedCheck_4051_;
goto v_resetjp_4043_;
}
else
{
lean_dec(v_pos_4023_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4051_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4049_; 
v___x_4046_ = lean_unsigned_to_nat(1u);
v___x_4047_ = lean_nat_add(v_idx_4029_, v___x_4046_);
lean_dec(v_idx_4029_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 1, v___x_4047_);
v___x_4049_ = v___x_4044_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_array_4028_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v___x_4047_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
v_pos_3993_ = v___x_4049_;
v_res_3994_ = v_res_4024_;
goto v___jp_3992_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_pos_4055_; lean_object* v_res_4056_; 
v_pos_4055_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_pos_4055_);
v_res_4056_ = lean_ctor_get(v___x_4022_, 1);
lean_inc(v_res_4056_);
lean_dec_ref_known(v___x_4022_, 2);
v_pos_3993_ = v_pos_4055_;
v_res_3994_ = v_res_4056_;
goto v___jp_3992_;
}
else
{
lean_object* v_pos_4057_; lean_object* v_err_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
v_pos_4057_ = lean_ctor_get(v___x_4022_, 0);
v_err_4058_ = lean_ctor_get(v___x_4022_, 1);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4022_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_err_4058_);
lean_inc(v_pos_4057_);
lean_dec(v___x_4022_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_pos_4057_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_err_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
v___jp_3977_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3979_ = ((lean_object*)(l_Std_Http_Protocol_H1_parseRequestLine___closed__1));
v___x_3980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___y_3978_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
return v___x_3980_;
}
v___jp_3981_:
{
if (v___y_3983_ == 0)
{
lean_dec(v___y_3985_);
lean_dec(v___y_3982_);
v___y_3978_ = v___y_3984_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_3986_; uint8_t v___x_3987_; 
v___x_3986_ = lean_unsigned_to_nat(0u);
v___x_3987_ = lean_nat_dec_eq(v___y_3985_, v___x_3986_);
lean_dec(v___y_3985_);
if (v___x_3987_ == 0)
{
lean_dec(v___y_3982_);
v___y_3978_ = v___y_3984_;
goto v___jp_3977_;
}
else
{
uint8_t v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3988_ = 0;
v___x_3989_ = l_Std_Http_Headers_empty;
v___x_3990_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3990_, 0, v___y_3982_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
lean_ctor_set_uint8(v___x_3990_, sizeof(void*)*2, v___x_3988_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___y_3984_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
return v___x_3991_;
}
}
}
v___jp_3992_:
{
lean_object* v_fst_3995_; lean_object* v_snd_3996_; lean_object* v___x_3997_; 
v_fst_3995_ = lean_ctor_get(v_res_3994_, 0);
lean_inc(v_fst_3995_);
v_snd_3996_ = lean_ctor_get(v_res_3994_, 1);
lean_inc(v_snd_3996_);
lean_dec_ref(v_res_3994_);
v___x_3997_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_3975_, v_pos_3993_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_pos_3998_; lean_object* v_res_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4012_; 
v_pos_3998_ = lean_ctor_get(v___x_3997_, 0);
v_res_3999_ = lean_ctor_get(v___x_3997_, 1);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4001_ = v___x_3997_;
v_isShared_4002_ = v_isSharedCheck_4012_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_res_3999_);
lean_inc(v_pos_3998_);
lean_dec(v___x_3997_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4012_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_4003_ = lean_unsigned_to_nat(1u);
v___x_4004_ = lean_nat_dec_eq(v_fst_3995_, v___x_4003_);
lean_dec(v_fst_3995_);
if (v___x_4004_ == 0)
{
lean_del_object(v___x_4001_);
v___y_3982_ = v_res_3999_;
v___y_3983_ = v___x_4004_;
v___y_3984_ = v_pos_3998_;
v___y_3985_ = v_snd_3996_;
goto v___jp_3981_;
}
else
{
uint8_t v___x_4005_; 
v___x_4005_ = lean_nat_dec_eq(v_snd_3996_, v___x_4003_);
if (v___x_4005_ == 0)
{
lean_del_object(v___x_4001_);
v___y_3982_ = v_res_3999_;
v___y_3983_ = v___x_4004_;
v___y_3984_ = v_pos_3998_;
v___y_3985_ = v_snd_3996_;
goto v___jp_3981_;
}
else
{
uint8_t v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4010_; 
lean_dec(v_snd_3996_);
v___x_4006_ = 1;
v___x_4007_ = l_Std_Http_Headers_empty;
v___x_4008_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4008_, 0, v_res_3999_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
lean_ctor_set_uint8(v___x_4008_, sizeof(void*)*2, v___x_4006_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 1, v___x_4008_);
v___x_4010_ = v___x_4001_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_pos_3998_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v___x_4008_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
else
{
lean_object* v_pos_4013_; lean_object* v_err_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec(v_snd_3996_);
lean_dec(v_fst_3995_);
v_pos_4013_ = lean_ctor_get(v___x_3997_, 0);
v_err_4014_ = lean_ctor_get(v___x_3997_, 1);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3997_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_err_4014_);
lean_inc(v_pos_4013_);
lean_dec(v___x_3997_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_pos_4013_);
lean_ctor_set(v_reuseFailAlloc_4020_, 1, v_err_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLine___boxed(lean_object* v_limits_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Std_Http_Protocol_H1_parseStatusLine(v_limits_4066_, v_a_4067_);
lean_dec_ref(v_limits_4066_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion(lean_object* v_limits_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_pos_4072_; lean_object* v_res_4073_; lean_object* v___x_4103_; 
v___x_4103_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseHttpVersionNumber(v_a_4070_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_pos_4104_; lean_object* v_res_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4135_; 
v_pos_4104_ = lean_ctor_get(v___x_4103_, 0);
v_res_4105_ = lean_ctor_get(v___x_4103_, 1);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4107_ = v___x_4103_;
v_isShared_4108_ = v_isSharedCheck_4135_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_res_4105_);
lean_inc(v_pos_4104_);
lean_dec(v___x_4103_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4135_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v_array_4109_; lean_object* v_idx_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
v_array_4109_ = lean_ctor_get(v_pos_4104_, 0);
v_idx_4110_ = lean_ctor_get(v_pos_4104_, 1);
v___x_4111_ = lean_byte_array_size(v_array_4109_);
v___x_4112_ = lean_nat_dec_lt(v_idx_4110_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
lean_dec(v_res_4105_);
v___x_4113_ = lean_box(0);
if (v_isShared_4108_ == 0)
{
lean_ctor_set_tag(v___x_4107_, 1);
lean_ctor_set(v___x_4107_, 1, v___x_4113_);
v___x_4115_ = v___x_4107_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_pos_4104_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
else
{
uint8_t v___x_4117_; uint8_t v_got_4118_; uint8_t v___x_4119_; 
v___x_4117_ = 32;
v_got_4118_ = lean_byte_array_fget(v_array_4109_, v_idx_4110_);
v___x_4119_ = lean_uint8_dec_eq(v_got_4118_, v___x_4117_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
lean_dec(v_res_4105_);
v___x_4120_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_sp___closed__1));
if (v_isShared_4108_ == 0)
{
lean_ctor_set_tag(v___x_4107_, 1);
lean_ctor_set(v___x_4107_, 1, v___x_4120_);
v___x_4122_ = v___x_4107_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_pos_4104_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
else
{
lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4132_; 
lean_inc(v_idx_4110_);
lean_inc_ref(v_array_4109_);
lean_del_object(v___x_4107_);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_pos_4104_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; lean_object* v_unused_4134_; 
v_unused_4133_ = lean_ctor_get(v_pos_4104_, 1);
lean_dec(v_unused_4133_);
v_unused_4134_ = lean_ctor_get(v_pos_4104_, 0);
lean_dec(v_unused_4134_);
v___x_4125_ = v_pos_4104_;
v_isShared_4126_ = v_isSharedCheck_4132_;
goto v_resetjp_4124_;
}
else
{
lean_dec(v_pos_4104_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4132_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4127_ = lean_unsigned_to_nat(1u);
v___x_4128_ = lean_nat_add(v_idx_4110_, v___x_4127_);
lean_dec(v_idx_4110_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 1, v___x_4128_);
v___x_4130_ = v___x_4125_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_array_4109_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
v_pos_4072_ = v___x_4130_;
v_res_4073_ = v_res_4105_;
goto v___jp_4071_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_pos_4136_; lean_object* v_res_4137_; 
v_pos_4136_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_pos_4136_);
v_res_4137_ = lean_ctor_get(v___x_4103_, 1);
lean_inc(v_res_4137_);
lean_dec_ref_known(v___x_4103_, 2);
v_pos_4072_ = v_pos_4136_;
v_res_4073_ = v_res_4137_;
goto v___jp_4071_;
}
else
{
lean_object* v_pos_4138_; lean_object* v_err_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
v_pos_4138_ = lean_ctor_get(v___x_4103_, 0);
v_err_4139_ = lean_ctor_get(v___x_4103_, 1);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4103_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_err_4139_);
lean_inc(v_pos_4138_);
lean_dec(v___x_4103_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_pos_4138_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_err_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
v___jp_4071_:
{
lean_object* v_fst_4074_; lean_object* v_snd_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4102_; 
v_fst_4074_ = lean_ctor_get(v_res_4073_, 0);
v_snd_4075_ = lean_ctor_get(v_res_4073_, 1);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_res_4073_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4077_ = v_res_4073_;
v_isShared_4078_ = v_isSharedCheck_4102_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_snd_4075_);
lean_inc(v_fst_4074_);
lean_dec(v_res_4073_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4102_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4079_; 
v___x_4079_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseStatusCode(v_limits_4069_, v_pos_4072_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_pos_4080_; lean_object* v_res_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4092_; 
v_pos_4080_ = lean_ctor_get(v___x_4079_, 0);
v_res_4081_ = lean_ctor_get(v___x_4079_, 1);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4083_ = v___x_4079_;
v_isShared_4084_ = v_isSharedCheck_4092_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_res_4081_);
lean_inc(v_pos_4080_);
lean_dec(v___x_4079_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4092_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4085_ = l_Std_Http_Version_ofNumber_x3f(v_fst_4074_, v_snd_4075_);
lean_dec(v_snd_4075_);
lean_dec(v_fst_4074_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 1, v___x_4085_);
lean_ctor_set(v___x_4077_, 0, v_res_4081_);
v___x_4087_ = v___x_4077_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_res_4081_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4089_; 
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 1, v___x_4087_);
v___x_4089_ = v___x_4083_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_pos_4080_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v___x_4087_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
else
{
lean_object* v_pos_4093_; lean_object* v_err_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_del_object(v___x_4077_);
lean_dec(v_snd_4075_);
lean_dec(v_fst_4074_);
v_pos_4093_ = lean_ctor_get(v___x_4079_, 0);
v_err_4094_ = lean_ctor_get(v___x_4079_, 1);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4079_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_err_4094_);
lean_inc(v_pos_4093_);
lean_dec(v___x_4079_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_pos_4093_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v_err_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseStatusLineRawVersion___boxed(lean_object* v_limits_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Std_Http_Protocol_H1_parseStatusLineRawVersion(v_limits_4147_, v_a_4148_);
lean_dec_ref(v_limits_4147_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_parseLastChunkBody(lean_object* v_limits_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v_maxTrailerHeaders_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_maxTrailerHeaders_4152_ = lean_ctor_get(v_limits_4150_, 17);
lean_inc(v_maxTrailerHeaders_4152_);
v___x_4153_ = lean_alloc_closure((void*)(l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_parseTrailerHeader___boxed), 2, 1);
lean_closure_set(v___x_4153_, 0, v_limits_4150_);
v___x_4154_ = l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_manyItems___redArg(v___x_4153_, v_maxTrailerHeaders_4152_, v_a_4151_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_pos_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v_pos_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_pos_4155_);
lean_dec_ref_known(v___x_4154_, 2);
v___x_4156_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1, &l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1_once, _init_l___private_Std_Http_Protocol_H1_Parser_0__Std_Http_Protocol_H1_crlf___closed__1);
v___x_4157_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_4156_, v_pos_4155_);
return v___x_4157_;
}
else
{
lean_object* v_pos_4158_; lean_object* v_err_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
v_pos_4158_ = lean_ctor_get(v___x_4154_, 0);
v_err_4159_ = lean_ctor_get(v___x_4154_, 1);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4154_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_err_4159_);
lean_inc(v_pos_4158_);
lean_dec(v___x_4154_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_pos_4158_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_err_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
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
